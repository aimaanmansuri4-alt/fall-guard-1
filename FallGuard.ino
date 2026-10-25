#include "fall_model.h"
#include <Arduino.h>
#include <Wire.h>
#include <WiFi.h>
#include <WiFiClientSecure.h>
#include <Preferences.h>
#include <UniversalTelegramBot.h>
#include <TinyGPSPlus.h>
#include <MAX30105.h>
#include <heartRate.h>
#include <Adafruit_GFX.h>

#define OLED_IS_SH1106 1

#if OLED_IS_SH1106
#include <Adafruit_SH110X.h>
#define OLED_WHITE SH110X_WHITE
#else
#include <Adafruit_SSD1306.h>
#define OLED_WHITE SSD1306_WHITE
#endif

#define BOT_TOKEN     "api token key"
#define DEFAULT_SSID  "vivo"
#define DEFAULT_PASS  "12345678"
#define PAIR_PIN      "4821"
#define ADMIN_PASS    "admin@123"

#define SDA_PIN 4
#define SCL_PIN 5
#define GPS_RX  7
#define GPS_TX  6
#define BUZZER  10
#define LED_R   0
#define LED_G   1
#define LED_B   3
#define OLED_ADDR 0x3C

#define IMPACT_G        2.5f
#define IMPACT_GYRO     300.0f
#define TILT_DROP       45.0f
#define SETTLE_MS       1500
#define WATCH_MS        12000
#define LYING_TILT      55.0f
#define STILL_G         0.15f
#define STILL_GYRO      40.0f
#define LIE_HOLD_MS     3000
#define PRE_ALARM_MS    15000
#define ALARM_MAX_MS    180000

#define BOOT_WIFI_MAX_MS   90000
#define WIFI_TRY_MS        12000

#define MAX_G 4
#define LOG_LINES 40
#define FW_VERSION "1.6"
static float bAx[FALL_WIN], bAy[FALL_WIN], bAz[FALL_WIN], bGx[FALL_WIN], bGy[FALL_WIN], bGz[FALL_WIN];
static int bIdx = 0; static uint32_t bCount = 0; static bool mlFall = false;

Preferences prefs;
TinyGPSPlus gps;
MAX30105 pox;
WiFiClientSecure secured;
UniversalTelegramBot bot(BOT_TOKEN, secured);
#if OLED_IS_SH1106
Adafruit_SH1106G oled(128, 64, &Wire, -1);
#else
Adafruit_SSD1306 oled(128, 64, &Wire, -1);
#endif
bool oledOk = false;

StaticSemaphore_t mtxBuf, logMtxBuf;
SemaphoreHandle_t mtx = nullptr, logMtx = nullptr;

enum { F_IDLE = 0, F_WATCH, F_PENDING, F_ALARM };
const char* FALL_NAMES[] = {"idle", "watching", "pending", "ALARM"};

float gbx = 0, gby = 0, gbz = 0;
uint8_t fallState = F_IDLE;
uint32_t tImpact = 0, stillSince = 0, tPending = 0, tAlarm = 0;
float gf = 0;
float tiltHist[50]; int tiltIdx = 0; bool tiltFull = false;
uint32_t uprightSince = 0;
long lastBeat = 0; int rates[4] = {0, 0, 0, 0}; int rateSpot = 0;
int bpmNow = 0; bool fingerNow = false; uint32_t lastBeatOk = 0;
uint32_t lastMpu = 0, lastShare = 0, lastLogStatus = 0, lastLogPoint = 0;
bool mpuOk = false, pulseOk = false;
float cAx = 0, cAy = 0, cAz = 1, cGx = 0, cGy = 0, cGz = 0, cAmag = 1, cGmag = 0, cTilt = 0;

volatile uint8_t wifiState = 0;
volatile uint32_t wifiRetryAt = 0;
volatile bool bootAnnounce = false;

struct Shared {
  float ax = 0, ay = 0, az = 1, gx = 0, gy = 0, gz = 0, amag = 1, gmag = 0, tilt = 0;
  int bpm = 0; bool finger = false, mpuOk = false, pulseOk = false;
  bool fix = false; double lat = 0, lon = 0; float kmph = 0; int sats = 0;
  bool haveLast = false; double llat = 0, llon = 0; char ltime[28] = {0}; bool locDirty = false;
  uint8_t fall = 0;
};
Shared S;
volatile bool cancelFlag = false, alertFlag = false;

String logbuf[LOG_LINES];
uint32_t logCount = 0;

String senderId = "", gId[MAX_G];
String uSsid = "", uPass = "";
struct Adm { String id; uint32_t until; } adm[3];
uint8_t admFails = 0; uint32_t admLockUntil = 0;
String liveChat = ""; uint32_t liveIdx = 0, lastLive = 0;
uint32_t lastWifiTry = 0, lastPoll = 0, lastOnlineMsg = 0;

volatile bool senderPaired = false;
volatile int  guardCount = 0;

void dlog(const char* fmt, ...) {
  char b[160];
  va_list ap; va_start(ap, fmt); vsnprintf(b, sizeof b, fmt, ap); va_end(ap);
  Serial.println(b);
  xSemaphoreTake(logMtx, portMAX_DELAY);
  logbuf[logCount % LOG_LINES] = String(millis() / 1000) + "s " + b;
  logCount++;
  xSemaphoreGive(logMtx);
}

String logRange(uint32_t from, uint32_t to) {
  String out;
  xSemaphoreTake(logMtx, portMAX_DELAY);
  for (uint32_t i = from; i < to; i++) out += logbuf[i % LOG_LINES] + "\n";
  xSemaphoreGive(logMtx);
  return out;
}

Shared snap() {
  xSemaphoreTake(mtx, portMAX_DELAY);
  Shared c = S;
  xSemaphoreGive(mtx);
  return c;
}

void setRGB(bool r, bool g, bool b) {
  digitalWrite(LED_R, r ? HIGH : LOW);
  digitalWrite(LED_G, g ? HIGH : LOW);
  digitalWrite(LED_B, b ? HIGH : LOW);
}

void ledStep(uint32_t now) {
  if (fallState == F_PENDING || fallState == F_ALARM) {
    bool on = (now / 250) % 2;
    setRGB(on, false, false);
    return;
  }
  if (WiFi.status() != WL_CONNECTED) setRGB(true, true, false);
  else if (!senderPaired)            setRGB(false, false, true);
  else                               setRGB(false, true, false);
}

String wifiWord() {
  if (WiFi.status() == WL_CONNECTED) return "ONLINE";
  if (wifiState == 1) return "CONNECTING";
  return "OFFLINE";
}

int signalLevel() {
  if (WiFi.status() != WL_CONNECTED) return 0;
  int r = WiFi.RSSI();
  if (r > -60) return 4;
  if (r > -70) return 3;
  if (r > -80) return 2;
  if (r > -90) return 1;
  return 0;
}

void drawBars(int x, int y, int level) {
  for (int i = 0; i < 4; i++) {
    int h = 2 + i * 2;
    int bx = x + i * 5, by = y + 8 - h;
    if (i < level) oled.fillRect(bx, by, 3, h, OLED_WHITE);
    else           oled.drawRect(bx, by, 3, h, OLED_WHITE);
  }
}

void oledFrame(const String& title, const String& l1, const String& l2, const String& l3, const String& l4) {
  oled.clearDisplay();
  oled.setTextColor(OLED_WHITE);
  oled.setTextSize(1);

  oled.setCursor(0, 0);  oled.print(title);
  drawBars(116, 0, signalLevel());
  oled.drawFastHLine(0, 10, 128, OLED_WHITE);

  oled.setCursor(0, 14); oled.println(l1);
  oled.setCursor(0, 24); oled.println(l2);
  oled.setCursor(0, 34); oled.println(l3);
  oled.setCursor(0, 44); oled.println(l4);

  oled.drawFastHLine(0, 53, 128, OLED_WHITE);
  oled.setCursor(0, 56);
  oled.print("WiFi: " + wifiWord());
  if (WiFi.status() == WL_CONNECTED) {
    oled.print("  " + String(WiFi.RSSI()) + "dBm");
  } else if (wifiState != 1 && wifiRetryAt != 0) {
    long secs = ((long)(wifiRetryAt - millis())) / 1000;
    if (secs > 0) oled.print("  retry " + String(secs) + "s");
  }
  oled.display();
}

void oledStep(uint32_t now) {
  static uint32_t lastOled = 0;
  if (!oledOk || now - lastOled < 1000) return;
  lastOled = now;

  if (fallState == F_PENDING || fallState == F_ALARM) {
    oled.clearDisplay();
    oled.setTextColor(OLED_WHITE);
    oled.setTextSize(2);
    oled.setCursor(0, 4);  oled.println("FALL!");
    oled.setTextSize(1);
    oled.setCursor(0, 30); oled.println(fallState == F_ALARM ? "Alert sent to guardians" : "Pre-alarm: cancel now");
    oled.setCursor(0, 42); oled.println("Send /ok in Telegram");
    oled.drawFastHLine(0, 53, 128, OLED_WHITE);
    oled.setCursor(0, 56);
    oled.print("WiFi: " + wifiWord());
    oled.display();
    return;
  }

  int page = (now / 4000) % 3;
  if (page == 0) {
    if (!senderPaired) {
      oledFrame("PAIRING",
                "Owner PIN: " + String(PAIR_PIN),
                "Bot: /sender " + String(PAIR_PIN),
                "Guardians: " + String(guardCount) + "/" + String(MAX_G),
                "Not paired yet");
    } else {
      oledFrame("PAIRING",
                "Owner: paired",
                "Guardians: " + String(guardCount) + "/" + String(MAX_G),
                "Guardian PIN: " + String(PAIR_PIN),
                "Bot: /guardian " + String(PAIR_PIN));
    }
  } else if (page == 1) {
    bool online = WiFi.status() == WL_CONNECTED;
    oledFrame("WIFI",
              online ? "SSID: " + WiFi.SSID() : String("SSID: (none)"),
              online ? "IP: " + WiFi.localIP().toString() : String("IP: -"),
              online ? "Signal: " + String(WiFi.RSSI()) + " dBm" : String(wifiState == 1 ? "Connecting..." : "Not connected"),
              "Fall: " + String(FALL_NAMES[fallState]));
  } else {
    bool fing = fingerNow;
    oledFrame("VITALS",
              fing ? "Pulse: " + String(bpmNow) + " bpm" : String("Pulse: no finger"),
              "Tilt: " + String((int)cTilt) + " deg",
              "Accel: " + String(cAmag, 2) + " g",
              "Uptime: " + String(millis() / 1000) + " s");
  }
}

void bootScreen(const String& l1, const String& l2) {
  if (!oledOk) return;
  oled.clearDisplay();
  oled.setTextColor(OLED_WHITE);
  oled.setTextSize(1);
  oled.setCursor(0, 8);  oled.println("FallGuard starting");
  oled.drawFastHLine(0, 20, 128, OLED_WHITE);
  oled.setCursor(0, 28); oled.println(l1);
  oled.setCursor(0, 42); oled.println(l2);
  oled.display();
}

bool mpuReadRaw(float* a, float* g) {
  Wire.beginTransmission(0x68); Wire.write(0x3B);
  if (Wire.endTransmission(false) != 0) return false;
  if (Wire.requestFrom(0x68, 14, 1) != 14) return false;
  int16_t v[7];
  for (int i = 0; i < 7; i++) {
    uint8_t h = Wire.read(), l = Wire.read();
    v[i] = (int16_t)((h << 8) | l);
  }
  a[0] = v[0] / 4096.0f; a[1] = v[1] / 4096.0f; a[2] = v[2] / 4096.0f;
  g[0] = v[4] / 32.8f;   g[1] = v[5] / 32.8f;   g[2] = v[6] / 32.8f;
  return true;
}

void mpuInit() {
  Wire.beginTransmission(0x68); Wire.write(0x75);
  if (Wire.endTransmission(false) != 0 || Wire.requestFrom(0x68, 1, 1) != 1) { dlog("MPU6050 not found"); return; }
  uint8_t who = Wire.read();
  if (who == 0x00 || who == 0xFF) { dlog("MPU6050 bad id 0x%02X", who); return; }
  auto wr = [](uint8_t r, uint8_t v) { Wire.beginTransmission(0x68); Wire.write(r); Wire.write(v); Wire.endTransmission(); };
  wr(0x6B, 0x00); delay(50);
  wr(0x1A, 0x03);
  wr(0x1B, 0x10);
  wr(0x1C, 0x10);
  float a[3], g[3], sx = 0, sy = 0, sz = 0; int n = 0;
  for (int i = 0; i < 100; i++) { if (mpuReadRaw(a, g)) { sx += g[0]; sy += g[1]; sz += g[2]; n++; } delay(10); }
  if (n > 0) { gbx = sx / n; gby = sy / n; gbz = sz / n; }
  mpuOk = true;
  dlog("MPU6050 ok (id 0x%02X), gyro bias %.1f %.1f %.1f", who, gbx, gby, gbz);
}

void pulseInit() {
  if (!pox.begin(Wire, I2C_SPEED_FAST)) { dlog("MAX30102 not found"); return; }
  pox.setup();
  pox.setPulseAmplitudeRed(0x1F);
  pox.setPulseAmplitudeGreen(0);
  pulseOk = true;
  dlog("MAX30102 ok");
}

void oledInit() {
#if OLED_IS_SH1106
  oledOk = oled.begin(OLED_ADDR, true);
#else
  oledOk = oled.begin(SSD1306_SWITCHCAPVCC, OLED_ADDR);
#endif
  if (!oledOk) { dlog("OLED not found at 0x%02X", OLED_ADDR); return; }
  oled.clearDisplay();
  oled.display();
  oled.setTextColor(OLED_WHITE);
  oled.setTextSize(1);
  oled.setCursor(0, 20); oled.println("FallGuard starting...");
  oled.display();
  dlog("OLED ok");
}

void pulseStep() {
  if (!pulseOk) return;
  long ir = pox.getIR();
  if (ir > 50000) {
    fingerNow = true;
    if (checkForBeat(ir)) {
      long delta = millis() - lastBeat; lastBeat = millis();
      float b = 60.0f / (delta / 1000.0f);
      if (b > 30 && b < 220) {
        rates[rateSpot++ % 4] = (int)b;
        int sum = 0; for (int i = 0; i < 4; i++) sum += rates[i];
        int cnt = 0; for (int i = 0; i < 4; i++) if (rates[i] > 0) cnt++;
        bpmNow = sum / max(cnt, 1);
        lastBeatOk = millis();
      }
    }
    if (millis() - lastBeatOk > 6000) bpmNow = 0;
  } else {
    fingerNow = false; bpmNow = 0; rateSpot = 0;
    for (int i = 0; i < 4; i++) rates[i] = 0;
  }
}

void mpuStep(uint32_t now) {
  if (cancelFlag) {
    cancelFlag = false;
    if (fallState != F_IDLE) { fallState = F_IDLE; dlog("fall cancelled"); }
  }
  if (!mpuOk) return;
  float a[3], g[3];
  if (!mpuReadRaw(a, g)) return;
  cAx = a[0]; cAy = a[1]; cAz = a[2];
  cGx = g[0] - gbx; cGy = g[1] - gby; cGz = g[2] - gbz;
  cAmag = sqrtf(cAx * cAx + cAy * cAy + cAz * cAz);
  cGmag = sqrtf(cGx * cGx + cGy * cGy + cGz * cGz);
  cTilt = atan2f(sqrtf(cAx * cAx + cAy * cAy), cAz) * 57.2957795f;
  gf = 0.8f * gf + 0.2f * cGmag;
  float tiltOld = tiltFull ? tiltHist[tiltIdx] : cTilt;
  tiltHist[tiltIdx] = cTilt; tiltIdx = (tiltIdx + 1) % 50; if (tiltIdx == 0) tiltFull = true;

  switch (fallState) {
    case F_IDLE:
      if (mlFall || cAmag > IMPACT_G || cGmag > IMPACT_GYRO || (cTilt - tiltOld) > TILT_DROP) {
        fallState = F_WATCH; tImpact = mlFall ? now - 1000 : now; stillSince = 0;
        dlog("trigger ml=%d a=%.2f g gyro=%.0f dps tilt=%.0f", mlFall, cAmag, cGmag, cTilt);
        mlFall = false;
      }
      break;
    case F_WATCH: {
      uint32_t el = now - tImpact;
      if (el < SETTLE_MS) break;
      if (el > WATCH_MS) { fallState = F_IDLE; dlog("no lying after impact, ignored"); break; }
      bool lying = cTilt > LYING_TILT;
      bool still = fabsf(cAmag - 1.0f) < STILL_G && gf < STILL_GYRO;
      if (lying && still) {
        if (stillSince == 0) stillSince = now;
        else if (now - stillSince >= LIE_HOLD_MS) {
          fallState = F_PENDING; tPending = now; uprightSince = 0;
          dlog("fall suspected, pre-alarm started");
        }
      } else stillSince = 0;
      if (el > 3000 && cTilt < 35.0f && gf > 60.0f) { fallState = F_IDLE; dlog("upright again, ignored"); }
      break;
    }
    case F_PENDING:
      if (cTilt < 35.0f) {
        if (uprightSince == 0) uprightSince = now;
        else if (now - uprightSince > 1500) { fallState = F_IDLE; dlog("upright again, cancelled"); break; }
      } else uprightSince = 0;
      if (now - tPending > PRE_ALARM_MS) {
        fallState = F_ALARM; tAlarm = now; alertFlag = true;
        dlog("FALL ALERT raised");
      }
      break;
    case F_ALARM:
      if (now - tAlarm > ALARM_MAX_MS) { fallState = F_IDLE; dlog("alarm timeout"); }
      break;
  }
}

void buzzerStep(uint32_t now) {
  bool on = false;
  if (fallState == F_PENDING) on = (now / 150) % 2;
  else if (fallState == F_ALARM) on = (now / 500) % 2;
  digitalWrite(BUZZER, on ? HIGH : LOW);
}

void gpsTimeStr(char* out, size_t n) {
  if (gps.date.isValid() && gps.time.isValid() && gps.date.year() > 2020)
    snprintf(out, n, "%04d-%02d-%02d %02d:%02d UTC", gps.date.year(), gps.date.month(), gps.date.day(),
             gps.time.hour(), gps.time.minute());
  else snprintf(out, n, "uptime %lus", (unsigned long)(millis() / 1000));
}

void shareStep() {
  bool fix = gps.location.isValid() && gps.location.age() < 3000;
  static double lastLat = 0, lastLon = 0;
  bool newLast = false; char tbuf[28] = {0};
  if (fix) {
    double la = gps.location.lat(), lo = gps.location.lng();
    uint32_t now = millis();
    double moved = (lastLat == 0 && lastLon == 0) ? 1e9 : TinyGPSPlus::distanceBetween(la, lo, lastLat, lastLon);
    if (lastLogPoint == 0 || (now - lastLogPoint > 120000 && moved > 15) || now - lastLogPoint > 600000) {
      newLast = true; lastLogPoint = now; lastLat = la; lastLon = lo; gpsTimeStr(tbuf, sizeof tbuf);
      dlog("location logged %.6f,%.6f", la, lo);
    }
  }
  xSemaphoreTake(mtx, portMAX_DELAY);
  S.ax = cAx; S.ay = cAy; S.az = cAz; S.gx = cGx; S.gy = cGy; S.gz = cGz;
  S.amag = cAmag; S.gmag = cGmag; S.tilt = cTilt;
  S.bpm = bpmNow; S.finger = fingerNow; S.mpuOk = mpuOk; S.pulseOk = pulseOk;
  S.fix = fix; S.sats = gps.satellites.isValid() ? gps.satellites.value() : 0;
  if (fix) { S.lat = gps.location.lat(); S.lon = gps.location.lng(); S.kmph = gps.speed.kmph(); }
  if (newLast) {
    S.haveLast = true; S.llat = S.lat; S.llon = S.lon;
    strncpy(S.ltime, tbuf, sizeof S.ltime - 1); S.locDirty = true;
  }
  S.fall = fallState;
  xSemaphoreGive(mtx);

  if (millis() - lastLogStatus > 10000) {
    lastLogStatus = millis();
    dlog("a=%.2fg gy=%.0f tilt=%.0f bpm=%d fix=%d sat=%d st=%s wifi=%d",
         cAmag, cGmag, cTilt, bpmNow, fix, S.sats, FALL_NAMES[fallState], WiFi.status() == WL_CONNECTED);
  }
}

String mapLink(double la, double lo) { return "https://maps.google.com/?q=" + String(la, 6) + "," + String(lo, 6); }

String pulseText(const Shared& s) {
  if (!s.pulseOk) return "Pulse: sensor not found";
  if (!s.finger) return "Pulse: no finger on sensor";
  if (s.bpm <= 0) return "Pulse: reading...";
  return "Pulse: " + String(s.bpm) + " bpm";
}
String lastText(const Shared& s) {
  if (!s.haveLast) return "No location logged yet.";
  return "Last logged: " + String(s.llat, 6) + ", " + String(s.llon, 6) + " at " + String(s.ltime) + "\n" + mapLink(s.llat, s.llon);
}
String gpsText(const Shared& s) {
  if (s.fix) return "GPS: " + String(s.lat, 6) + ", " + String(s.lon, 6) + "\nSats " + String(s.sats) + ", " +
                    String(s.kmph, 1) + " km/h\n" + mapLink(s.lat, s.lon);
  return "GPS: no fix (sats " + String(s.sats) + ")\n" + lastText(s);
}
String mpuText(const Shared& s) {
  if (!s.mpuOk) return "Motion: sensor not found";
  return "Motion: tilt " + String((int)s.tilt) + " deg, accel " + String(s.amag, 2) + " g, gyro " +
         String((int)s.gmag) + " dps\nFall state: " + FALL_NAMES[s.fall];
}
String locationText(const Shared& s) {
  if (s.fix) return "Location (live): " + String(s.lat, 6) + ", " + String(s.lon, 6) + "\n" + mapLink(s.lat, s.lon);
  return "No live GPS fix.\n" + lastText(s);
}
String statusText(const Shared& s) {
  String t = pulseText(s) + "\n";
  if (s.fix) t += "GPS: " + String(s.lat, 6) + ", " + String(s.lon, 6) + "\n";
  else t += "GPS: no fix" + String(s.haveLast ? " (last " + String(s.llat, 5) + ", " + String(s.llon, 5) + ")" : "") + "\n";
  t += mpuText(s) + "\nWiFi: " + WiFi.SSID() + " (" + String(WiFi.RSSI()) + " dBm)";
  return t;
}

void refreshPairCounts() {
  senderPaired = senderId.length() > 0;
  int c = 0; for (int i = 0; i < MAX_G; i++) if (gId[i].length()) c++;
  guardCount = c;
}
void loadPrefs() {
  prefs.begin("fg", false);
  senderId = prefs.getString("sender", "");
  for (int i = 0; i < MAX_G; i++) gId[i] = prefs.getString(("g" + String(i)).c_str(), "");
  uSsid = prefs.getString("ussid", ""); uPass = prefs.getString("upass", "");
  if (prefs.getBool("has", false)) {
    S.haveLast = true; S.llat = prefs.getDouble("lat", 0); S.llon = prefs.getDouble("lon", 0);
    prefs.getString("ltime", "").toCharArray(S.ltime, sizeof S.ltime);
  }
  refreshPairCounts();
}
void savePairs() {
  prefs.putString("sender", senderId);
  for (int i = 0; i < MAX_G; i++) prefs.putString(("g" + String(i)).c_str(), gId[i]);
  refreshPairCounts();
}
bool isSender(const String& c) { return senderId.length() && c == senderId; }
bool isGuardian(const String& c) { for (int i = 0; i < MAX_G; i++) if (gId[i].length() && gId[i] == c) return true; return false; }
int guardianCount() { int c = 0; for (int i = 0; i < MAX_G; i++) if (gId[i].length()) c++; return c; }
bool isPaired(const String& c) { return isSender(c) || isGuardian(c); }
bool isAdmin(const String& c) {
  for (int i = 0; i < 3; i++) if (adm[i].id == c && (int32_t)(adm[i].until - millis()) > 0) { adm[i].until = millis() + 600000; return true; }
  return false;
}
void grantAdmin(const String& c) {
  int slot = 0;
  for (int i = 0; i < 3; i++) { if (adm[i].id == c) { slot = i; break; } if ((int32_t)(adm[i].until - millis()) <= 0) slot = i; }
  adm[slot].id = c; adm[slot].until = millis() + 600000;
}
void persistLoc() {
  xSemaphoreTake(mtx, portMAX_DELAY);
  bool d = S.locDirty; double la = S.llat, lo = S.llon; char tb[28]; strncpy(tb, S.ltime, sizeof tb); tb[27] = 0;
  S.locDirty = false;
  xSemaphoreGive(mtx);
  if (!d) return;
  prefs.putDouble("lat", la); prefs.putDouble("lon", lo); prefs.putString("ltime", String(tb)); prefs.putBool("has", true);
}

void say(const String& chat, const String& text) {
  String t = text;
  while (t.length() > 3500) {
    int cut = t.lastIndexOf('\n', 3500); if (cut < 1) cut = 3500;
    bot.sendMessage(chat, t.substring(0, cut), "");
    t = t.substring(cut);
  }
  if (t.length()) bot.sendMessage(chat, t, "");
}
bool sayAll(const String& text) {
  bool any = false;
  if (senderId.length()) any |= bot.sendMessage(senderId, text, "");
  for (int i = 0; i < MAX_G; i++) if (gId[i].length()) any |= bot.sendMessage(gId[i], text, "");
  return any;
}

bool wifiTry(const String& ssid, const String& pass, uint32_t ms) {
  wifiState = 1;
  WiFi.disconnect(true, true);
  vTaskDelay(300 / portTICK_PERIOD_MS);
  WiFi.mode(WIFI_STA);
  WiFi.setAutoReconnect(false);
  WiFi.setTxPower(WIFI_POWER_8_5dBm);
  vTaskDelay(100 / portTICK_PERIOD_MS);
  WiFi.begin(ssid.c_str(), pass.c_str());
  uint32_t t = millis();
  while (WiFi.status() != WL_CONNECTED && millis() - t < ms) vTaskDelay(250 / portTICK_PERIOD_MS);
  bool ok = WiFi.status() == WL_CONNECTED;
  wifiState = ok ? 2 : 0;
  return ok;
}

void onWifiConnected() {
  secured.setInsecure();
  WiFi.setSleep(false);
  wifiRetryAt = 0;
  dlog("wifi ok: %s  %s  %d dBm", WiFi.SSID().c_str(), WiFi.localIP().toString().c_str(), WiFi.RSSI());
  if (millis() - lastOnlineMsg > 60000 || lastOnlineMsg == 0) {
    lastOnlineMsg = millis();
    sayAll("FallGuard online on " + WiFi.SSID() + ". IP: " + WiFi.localIP().toString());
  }
}

bool ensureWifi() {
  if (WiFi.status() == WL_CONNECTED) { wifiState = 2; return true; }
  wifiState = 0;
  if (lastWifiTry != 0 && millis() - lastWifiTry < 8000) return false;
  lastWifiTry = millis();
  bool ok = false;
  if (uSsid.length()) { dlog("wifi: trying saved '%s'", uSsid.c_str()); ok = wifiTry(uSsid, uPass, 15000); }
  if (!ok) { dlog("wifi: trying default '%s'", DEFAULT_SSID); ok = wifiTry(DEFAULT_SSID, DEFAULT_PASS, 15000); }
  if (ok) { onWifiConnected(); return true; }
  wifiRetryAt = millis() + 8000;
  return false;
}

void bootWifi() {
  WiFi.mode(WIFI_STA);
  WiFi.setAutoReconnect(false);
  WiFi.setTxPower(WIFI_POWER_8_5dBm);
  setRGB(true, true, false);

  uint32_t t0 = millis();
  int attempt = 0;
  while (WiFi.status() != WL_CONNECTED && millis() - t0 < BOOT_WIFI_MAX_MS) {
    attempt++;
    bool ok = false;
    if (uSsid.length()) {
      bootScreen("Try " + String(attempt) + ": " + uSsid, "Connecting WiFi...");
      dlog("boot wifi: trying saved '%s'", uSsid.c_str());
      ok = wifiTry(uSsid, uPass, WIFI_TRY_MS);
    }
    if (!ok) {
      bootScreen("Try " + String(attempt) + ": " + String(DEFAULT_SSID), "Connecting WiFi...");
      dlog("boot wifi: trying default '%s'", DEFAULT_SSID);
      ok = wifiTry(DEFAULT_SSID, DEFAULT_PASS, WIFI_TRY_MS);
    }
    if (ok) break;
    delay(2000);
  }

  if (WiFi.status() == WL_CONNECTED) {
    secured.setInsecure();
    WiFi.setSleep(false);
    wifiState = 2;
    wifiRetryAt = 0;
    bootAnnounce = true;
    dlog("boot wifi ok: %s %s %d dBm", WiFi.SSID().c_str(), WiFi.localIP().toString().c_str(), WiFi.RSSI());
    bootScreen("Connected: " + WiFi.SSID(), WiFi.localIP().toString());
    delay(1000);
  } else {
    wifiState = 0;
    dlog("boot wifi failed, continuing; net task will keep retrying");
    bootScreen("WiFi not found", "Will keep retrying");
    delay(1500);
  }
}

void changeWifi(const String& chat, const String& ssid, const String& pass) {
  String oldS = uSsid, oldP = uPass;
  say(chat, "Connecting to \"" + ssid + "\"... I will confirm here. If it fails I switch back.");
  bool ok = wifiTry(ssid, pass, 20000);
  if (ok) {
    uSsid = ssid; uPass = pass;
    prefs.putString("ussid", uSsid); prefs.putString("upass", uPass);
    secured.setInsecure();
    say(chat, "Connected to \"" + ssid + "\" (" + WiFi.localIP().toString() + "). Saved.");
    dlog("wifi changed to '%s'", ssid.c_str());
  } else {
    dlog("wifi change failed for '%s'", ssid.c_str());
    bool back = false;
    if (oldS.length()) back = wifiTry(oldS, oldP, 15000);
    if (!back) back = wifiTry(DEFAULT_SSID, DEFAULT_PASS, 15000);
    if (back) say(chat, "Could not connect to \"" + ssid + "\". Check the name and password, and that the hotspot is on (2.4 GHz). Still on \"" + WiFi.SSID() + "\".");
  }
}

String HELP_NEW =
  "FallGuard bot\n\nPick your side:\n/sender PIN - wearer / setup side\n/guardian PIN - guardian side\n\nAsk the device owner for the PIN.";
String HELP_SENDER =
  "Sender side\n/wifi NAME | PASSWORD - connect device to a hotspot\n/wifi - show current network\n/status - pulse, GPS, motion\n/pulse /gps /mpu /location\n/ok - cancel a fall alert\n/unpair";
String HELP_GUARD =
  "Guardian side\n/status - pulse, GPS, motion\n/pulse /gps /mpu\n/location - live or last logged position\n/ok - mark alert as handled\n/unpair";
String HELP_ADMIN =
  "Admin panel\n/serial [n] - last n serial lines (default 30)\n/live on|off - stream serial here\n/info - device info\n/forgetwifi - clear saved hotspot\n/reboot\n/logout";

void splitCmd(String t, String& cmd, String& args) {
  t.trim();
  int i = 0; while (i < (int)t.length() && t[i] != ' ' && t[i] != '\n') i++;
  cmd = t.substring(0, i); args = t.substring(i); args.trim();
  int at = cmd.indexOf('@'); if (at > 0) cmd = cmd.substring(0, at);
  cmd.toLowerCase();
}

void handleMsg(const String& chat, const String& text, const String& who) {
  String cmd, args; splitCmd(text, cmd, args);
  if (cmd.length() == 0 || cmd[0] != '/') { if (!isPaired(chat)) say(chat, HELP_NEW); return; }
  bool snd = isSender(chat), grd = isGuardian(chat);
  dlog("tg %s: %s", who.c_str(), cmd.c_str());

  if (cmd == "/start" || cmd == "/help") {
    String h = snd ? HELP_SENDER : (grd ? HELP_GUARD : HELP_NEW);
    if (isAdmin(chat)) h += "\n\n" + HELP_ADMIN;
    say(chat, h); return;
  }
  if (cmd == "/sender" || cmd == "/guardian") {
    if (args != PAIR_PIN) { say(chat, "Wrong PIN."); return; }
    if (cmd == "/sender") {
      senderId = chat; savePairs();
      say(chat, "You are the SENDER side.\n\n" + HELP_SENDER);
    } else {
      if (!grd) {
        int slot = -1; for (int i = 0; i < MAX_G; i++) if (!gId[i].length()) { slot = i; break; }
        if (slot < 0) { say(chat, "Guardian list is full (" + String(MAX_G) + ")."); return; }
        gId[slot] = chat; savePairs();
      }
      say(chat, "You are a GUARDIAN.\n\n" + HELP_GUARD);
    }
    return;
  }
  if (cmd == "/admin") {
    if ((int32_t)(admLockUntil - millis()) > 0) { say(chat, "Too many tries. Wait a minute."); return; }
    if (args == ADMIN_PASS) { admFails = 0; grantAdmin(chat); say(chat, "Admin unlocked for 10 minutes.\n\n" + HELP_ADMIN); }
    else { if (++admFails >= 3) { admFails = 0; admLockUntil = millis() + 60000; } say(chat, "Wrong password."); }
    return;
  }

  if (cmd == "/serial" || cmd == "/live" || cmd == "/info" || cmd == "/forgetwifi" || cmd == "/reboot" || cmd == "/logout") {
    if (!isAdmin(chat)) { say(chat, "Admin only. Send /admin PASSWORD first."); return; }
    if (cmd == "/serial") {
      int n = args.length() ? args.toInt() : 30; n = constrain(n, 1, LOG_LINES);
      uint32_t total = logCount; uint32_t from = total > (uint32_t)n ? total - n : 0;
      if (total > LOG_LINES && from < total - LOG_LINES) from = total - LOG_LINES;
      say(chat, logRange(from, total));
    } else if (cmd == "/live") {
      if (args == "on") { liveChat = chat; liveIdx = logCount; say(chat, "Live serial on. /live off to stop."); }
      else { liveChat = ""; say(chat, "Live serial off."); }
    } else if (cmd == "/info") {
      say(chat, "FallGuard v" FW_VERSION "\nWiFi: " + WiFi.SSID() + " " + WiFi.localIP().toString() + " (" + String(WiFi.RSSI()) + " dBm)" +
                "\nUptime: " + String(millis() / 1000) + " s\nFree heap: " + String(ESP.getFreeHeap()) +
                "\nSender paired: " + String(senderId.length() ? "yes" : "no") +
                "\nGuardians: " + String(guardianCount()));
    } else if (cmd == "/forgetwifi") {
      uSsid = ""; uPass = ""; prefs.remove("ussid"); prefs.remove("upass");
      say(chat, "Saved hotspot cleared. Using default network.");
      WiFi.disconnect(); lastWifiTry = 0;
    } else if (cmd == "/reboot") {
      say(chat, "Rebooting."); vTaskDelay(500 / portTICK_PERIOD_MS); ESP.restart();
    } else {
      for (int i = 0; i < 3; i++) if (adm[i].id == chat) adm[i].until = 0;
      if (liveChat == chat) liveChat = "";
      say(chat, "Admin locked.");
    }
    return;
  }

  if (!snd && !grd) { say(chat, HELP_NEW); return; }

  if (cmd == "/unpair") {
    if (snd) senderId = "";
    for (int i = 0; i < MAX_G; i++) if (gId[i] == chat) gId[i] = "";
    savePairs(); say(chat, "Unpaired."); return;
  }
  if (cmd == "/ok") {
    cancelFlag = true;
    say(chat, "Alert marked as handled.");
    String m = "Alert handled by " + who + ".";
    if (senderId.length() && senderId != chat) bot.sendMessage(senderId, m, "");
    for (int i = 0; i < MAX_G; i++) if (gId[i].length() && gId[i] != chat) bot.sendMessage(gId[i], m, "");
    return;
  }
  Shared s = snap();
  if (cmd == "/status") { say(chat, statusText(s)); return; }
  if (cmd == "/pulse")  { say(chat, pulseText(s)); return; }
  if (cmd == "/gps")    { say(chat, gpsText(s)); return; }
  if (cmd == "/mpu")    { say(chat, mpuText(s)); return; }
  if (cmd == "/location" || cmd == "/last") { say(chat, locationText(s)); return; }
  if (cmd == "/wifi") {
    if (!snd) { say(chat, "Only the sender side can change WiFi."); return; }
    if (args.length() == 0) {
      say(chat, "Network: " + WiFi.SSID() + " (" + String(WiFi.RSSI()) + " dBm)\nChange: /wifi NAME | PASSWORD"); return;
    }
    int bar = args.indexOf('|');
    String ssid = bar < 0 ? args : args.substring(0, bar), pass = bar < 0 ? "" : args.substring(bar + 1);
    ssid.trim(); pass.trim();
    if (ssid.length() == 0 || ssid.length() > 32) { say(chat, "Usage: /wifi NAME | PASSWORD"); return; }
    changeWifi(chat, ssid, pass);
    return;
  }
  say(chat, "Unknown command. /help");
}

void pollTelegram() {
  if (millis() - lastPoll < 1500) return;
  lastPoll = millis();
  int n = bot.getUpdates(bot.last_message_received + 1);
  while (n) {
    for (int i = 0; i < n; i++) {
      if (bot.messages[i].type != "message") continue;
      handleMsg(bot.messages[i].chat_id, bot.messages[i].text, bot.messages[i].from_name);
    }
    n = bot.getUpdates(bot.last_message_received + 1);
  }
}

void flushAlerts() {
  if (!alertFlag) return;
  Shared s = snap();
  String m = "FALL DETECTED\n" + pulseText(s) + "\n" + locationText(s) + "\n\nSend /ok when handled.";
  if (sayAll(m)) { alertFlag = false; dlog("alert sent"); }
}

void flushLive() {
  if (liveChat.length() == 0 || millis() - lastLive < 3000) return;
  lastLive = millis();
  if (!isAdmin(liveChat)) { liveChat = ""; return; }
  uint32_t total = logCount;
  if (total > LOG_LINES && liveIdx < total - LOG_LINES) liveIdx = total - LOG_LINES;
  if (total > liveIdx) { say(liveChat, logRange(liveIdx, total)); liveIdx = total; }
}

void netTask(void*) {
  for (;;) {
    if (ensureWifi()) {
      if (bootAnnounce) {
        bootAnnounce = false;
        lastOnlineMsg = millis();
        sayAll("FallGuard online on " + WiFi.SSID() + ". IP: " + WiFi.localIP().toString());
      }
      pollTelegram(); flushAlerts(); flushLive();
    }
    persistLoc();
    vTaskDelay(10 / portTICK_PERIOD_MS);
  }
}

void setup() {
  Serial.begin(115200);
  delay(1500);
  mtx    = xSemaphoreCreateMutexStatic(&mtxBuf);
  logMtx = xSemaphoreCreateMutexStatic(&logMtxBuf);
  Serial.printf("mutex ok: %d %d  free heap: %u\n", mtx != nullptr, logMtx != nullptr, ESP.getFreeHeap());

  pinMode(BUZZER, OUTPUT); digitalWrite(BUZZER, LOW);
  pinMode(LED_R, OUTPUT); pinMode(LED_G, OUTPUT); pinMode(LED_B, OUTPUT);
  setRGB(true, true, true);

  Wire.begin(SDA_PIN, SCL_PIN); Wire.setClock(400000);
  Serial1.setRxBufferSize(1024);
  Serial1.begin(9600, SERIAL_8N1, GPS_RX, GPS_TX);
  dlog("FallGuard v" FW_VERSION " boot");

  WiFi.onEvent([](arduino_event_id_t e, arduino_event_info_t info) {
    if (e == ARDUINO_EVENT_WIFI_STA_DISCONNECTED)
      dlog("wifi disc reason %d", info.wifi_sta_disconnected.reason);
  });

  loadPrefs();
  oledInit();

  bootWifi();

  mpuInit();
  pulseInit();
  digitalWrite(BUZZER, HIGH); delay(100); digitalWrite(BUZZER, LOW);
  setRGB(false, false, false);
  xTaskCreate(netTask, "net", 16384, NULL, 1, NULL);
}

void loop() {
  while (Serial1.available()) gps.encode(Serial1.read());
  pulseStep();
  uint32_t now = millis();
  if (now - lastMpu >= 20) { lastMpu = now; mpuStep(now); }
  buzzerStep(now);
  ledStep(now);
  oledStep(now);
  if (now - lastShare >= 100) { lastShare = now; shareStep(); }
  if (!pulseOk) delay(5);
}

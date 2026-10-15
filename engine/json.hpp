// Minimal JSON value + parser + writer, sufficient for the engine's JSONL
// protocol (objects, arrays, strings, numbers, booleans, null).
#pragma once
#include <cmath>
#include <map>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace mj {

struct Value {
  enum Type { NUL, BOOL, NUM, STR, ARR, OBJ } t = NUL;
  bool b = false;
  double num = 0;
  bool is_int = false;
  long long i = 0;
  std::string s;
  std::vector<Value> a;
  std::map<std::string, Value> o;

  bool has(const std::string& k) const { return t == OBJ && o.count(k); }
  const Value& operator[](const std::string& k) const {
    static Value nul;
    auto it = o.find(k);
    return it == o.end() ? nul : it->second;
  }
  long long as_int(long long def = 0) const { return t == NUM ? (is_int ? i : (long long)num) : def; }
  double as_num(double def = 0) const { return t == NUM ? num : def; }
  std::string as_str(const std::string& def = "") const { return t == STR ? s : def; }
  std::vector<int> as_ints() const {
    std::vector<int> v;
    if (t == ARR)
      for (auto& e : a) v.push_back((int)e.as_int());
    return v;
  }
};

struct Parser {
  const std::string& src;
  size_t p = 0;
  explicit Parser(const std::string& s) : src(s) {}
  void ws() {
    while (p < src.size() && (src[p] == ' ' || src[p] == '\t' || src[p] == '\n' || src[p] == '\r')) ++p;
  }
  [[noreturn]] void fail(const char* msg) { throw std::runtime_error(std::string("json: ") + msg); }
  Value parse() {
    ws();
    Value v = val();
    ws();
    return v;
  }
  Value val() {
    ws();
    if (p >= src.size()) fail("eof");
    char c = src[p];
    Value v;
    if (c == '{') {
      v.t = Value::OBJ;
      ++p;
      ws();
      if (src[p] == '}') {
        ++p;
        return v;
      }
      while (true) {
        ws();
        std::string k = str();
        ws();
        if (src[p] != ':') fail("expected :");
        ++p;
        v.o[k] = val();
        ws();
        if (src[p] == ',') {
          ++p;
          continue;
        }
        if (src[p] == '}') {
          ++p;
          break;
        }
        fail("expected , or }");
      }
    } else if (c == '[') {
      v.t = Value::ARR;
      ++p;
      ws();
      if (src[p] == ']') {
        ++p;
        return v;
      }
      while (true) {
        v.a.push_back(val());
        ws();
        if (src[p] == ',') {
          ++p;
          continue;
        }
        if (src[p] == ']') {
          ++p;
          break;
        }
        fail("expected , or ]");
      }
    } else if (c == '"') {
      v.t = Value::STR;
      v.s = str();
    } else if (src.compare(p, 4, "true") == 0) {
      v.t = Value::BOOL;
      v.b = true;
      p += 4;
    } else if (src.compare(p, 5, "false") == 0) {
      v.t = Value::BOOL;
      p += 5;
    } else if (src.compare(p, 4, "null") == 0) {
      p += 4;
    } else {
      size_t st = p;
      if (src[p] == '-') ++p;
      bool isint = true;
      while (p < src.size() && (isdigit((unsigned char)src[p]) || src[p] == '.' || src[p] == 'e' ||
                                src[p] == 'E' || src[p] == '+' || src[p] == '-')) {
        if (!isdigit((unsigned char)src[p])) isint = false;
        ++p;
      }
      if (st == p) fail("bad value");
      std::string tok = src.substr(st, p - st);
      v.t = Value::NUM;
      v.num = std::stod(tok);
      v.is_int = isint;
      if (isint) v.i = std::stoll(tok);
    }
    return v;
  }
  std::string str() {
    if (src[p] != '"') fail("expected string");
    ++p;
    std::string out;
    while (p < src.size() && src[p] != '"') {
      if (src[p] == '\\') {
        ++p;
        char e = src[p];
        if (e == 'n') out += '\n';
        else if (e == 't') out += '\t';
        else if (e == 'u') {
          out += '?';
          p += 4;
        } else out += e;
        ++p;
      } else out += src[p++];
    }
    ++p;
    return out;
  }
};

inline Value parse(const std::string& s) {
  Parser ps(s);
  return ps.parse();
}

// --- writer helpers -------------------------------------------------------
inline std::string esc(const std::string& s) {
  std::string o = "\"";
  for (char c : s) {
    if (c == '"' || c == '\\') o += '\\', o += c;
    else if (c == '\n') o += "\\n";
    else o += c;
  }
  return o + "\"";
}
template <class T>
inline std::string arr(const std::vector<T>& v) {
  std::string o = "[";
  for (size_t i = 0; i < v.size(); ++i) {
    if (i) o += ",";
    o += std::to_string((long long)v[i]);
  }
  return o + "]";
}

struct ObjWriter {
  std::string out = "{";
  bool first = true;
  void key(const std::string& k) {
    if (!first) out += ",";
    first = false;
    out += esc(k) + ":";
  }
  ObjWriter& raw(const std::string& k, const std::string& v) {
    key(k);
    out += v;
    return *this;
  }
  ObjWriter& str(const std::string& k, const std::string& v) { return raw(k, esc(v)); }
  ObjWriter& num(const std::string& k, double v) {
    std::ostringstream ss;
    ss.precision(10);
    ss << v;
    return raw(k, ss.str());
  }
  ObjWriter& integer(const std::string& k, long long v) { return raw(k, std::to_string(v)); }
  ObjWriter& boolean(const std::string& k, bool v) { return raw(k, v ? "true" : "false"); }
  template <class T>
  ObjWriter& ints(const std::string& k, const std::vector<T>& v) {
    return raw(k, arr(v));
  }
  std::string done() { return out + "}"; }
};

}  // namespace mj

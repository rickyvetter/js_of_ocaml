// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010-2014 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

// An OCaml string is an object with three fields:
// - tag 't'
// - length 'l'
// - contents 'c'
//
// The contents of the string can be either a JavaScript array or
// a JavaScript string. The length of this string can be less than the
// length of the OCaml string. In this case, remaining bytes are
// assumed to be zeroes. Arrays are mutable but consumes more memory
// than strings. A common pattern is to start from an empty string and
// progressively fill it from the start. Partial strings makes it
// possible to implement this efficiently.
//
// When converting to and from UTF-16, we keep track of whether the
// string is composed only of ASCII characters (in which case, no
// conversion needs to be performed) or not.
//
// The string tag can thus take the following values:
//   full string     BYTE | UNKNOWN:      0
//                   BYTE | ASCII:        9
//                   BYTE | NOT_ASCII:    8
//   string prefix   PARTIAL:             2
//   array           ARRAY:               4
//
// One can use bit masking to discriminate these different cases:
//   known_encoding(x) = x&8
//   is_ascii(x) =       x&1
//   kind(x) =           x&6

//Provides: caml_str_repeat
function caml_str_repeat(n, s) {
  if(n == 0) return "";
  if (s.repeat) {return s.repeat(n);} // ECMAscript 6 and Firefox 24+
  var r = "", l = 0;
  for(;;) {
    if (n & 1) r += s;
    n >>= 1;
    if (n == 0) return r;
    s += s;
    l++;
    if (l == 9) {
      s.slice(0,1); // flatten the string
      // then, the flattening of the whole string will be faster,
      // as it will be composed of larger pieces
    }
  }
}

//Provides: caml_subarray_to_jsbytes
//Weakdef
// Pre ECMAScript 5, [apply] would not support array-like object.
// In such setup, Typed_array would be implemented as polyfill, and [f.apply] would
// fail here. Mark the primitive as Weakdef, so that people can override it easily.
function caml_subarray_to_jsbytes (a, i, len) {
  var f = String.fromCharCode;
  if (i == 0 && len <= 4096 && len == a.length) return f.apply (null, a);
  var s = "";
  for (; 0 < len; i += 1024,len-=1024)
    s += f.apply (null, a.slice(i,i + Math.min(len, 1024)));
  return s;
}

//Provides: caml_jsbytes_to_array
function caml_jsbytes_to_array (s) {
  /* Assumes not ARRAY */
  if(globalThis.Uint8Array) {
    var a = new globalThis.Uint8Array(s.length);
  } else {
    var a = new Array(s.length);
  }
  var b = s, l = b.length, i = 0;
  for (; i < l; i++) a[i] = b.charCodeAt(i);
  return a;
}


//Provides: caml_utf8_of_utf16
function caml_utf8_of_utf16(s) {
  for (var b = "", t = b, c, d, i = 0, l = s.length; i < l; i++) {
    c = s.charCodeAt(i);
    if (c < 0x80) {
      for (var j = i + 1; (j < l) && (c = s.charCodeAt(j)) < 0x80; j++);
      if (j - i > 512) { t.substr(0, 1); b += t; t = ""; b += s.slice(i, j) }
      else t += s.slice(i, j);
      if (j == l) break;
      i = j;
    }
    if (c < 0x800) {
      t += String.fromCharCode(0xc0 | (c >> 6));
      t += String.fromCharCode(0x80 | (c & 0x3f));
    } else if (c < 0xd800 || c >= 0xdfff) {
      t += String.fromCharCode(0xe0 | (c >> 12),
                               0x80 | ((c >> 6) & 0x3f),
                               0x80 | (c & 0x3f));
    } else if (c >= 0xdbff || i + 1 == l ||
               (d = s.charCodeAt(i + 1)) < 0xdc00 || d > 0xdfff) {
      // Unmatched surrogate pair, replaced by \ufffd (replacement character)
      t += "\xef\xbf\xbd";
    } else {
      i++;
      c = (c << 10) + d - 0x35fdc00;
      t += String.fromCharCode(0xf0 | (c >> 18),
                               0x80 | ((c >> 12) & 0x3f),
                               0x80 | ((c >> 6) & 0x3f),
                               0x80 | (c & 0x3f));
    }
    if (t.length > 1024) {t.substr(0, 1); b += t; t = "";}
  }
  return b+t;
}

//Provides: caml_utf16_of_utf8
function caml_utf16_of_utf8(s) {
  for (var b = "", t = "", c, c1, c2, v, i = 0, l = s.length; i < l; i++) {
    c1 = s.charCodeAt(i);
    if (c1 < 0x80) {
      for (var j = i + 1; (j < l) && (c1 = s.charCodeAt(j)) < 0x80; j++);
      if (j - i > 512) { t.substr(0, 1); b += t; t = ""; b += s.slice(i, j) }
      else t += s.slice(i, j);
      if (j == l) break;
      i = j;
    }
    v = 1;
    if ((++i < l) && (((c2 = s.charCodeAt(i)) & -64) == 128)) {
      c = c2 + (c1 << 6);
      if (c1 < 0xe0) {
        v = c - 0x3080;
        if (v < 0x80) v = 1;
      } else {
        v = 2;
        if ((++i < l) && (((c2 = s.charCodeAt(i)) & -64) == 128)) {
          c = c2 + (c << 6);
          if (c1 < 0xf0) {
            v = c - 0xe2080;
            if ((v < 0x800) || ((v >= 0xd7ff) && (v < 0xe000))) v = 2;
          } else {
            v = 3;
            if ((++i < l) && (((c2 = s.charCodeAt(i)) & -64) == 128) &&
                (c1 < 0xf5)) {
              v = c2 - 0x3c82080 + (c << 6);
              if (v < 0x10000 || v > 0x10ffff) v = 3;
            }
          }
        }
      }
    }
    if (v < 4) { // Invalid sequence
      i -= v;
      t += "\ufffd";
    } else if (v > 0xffff)
      t += String.fromCharCode(0xd7c0 + (v >> 10), 0xdc00 + (v & 0x3FF))
    else
      t += String.fromCharCode(v);
    if (t.length > 1024) {t.substr(0, 1); b += t; t = "";}
  }
  return b+t;
}

//Provides: jsoo_is_ascii
function jsoo_is_ascii (s) {
  // The regular expression gets better at around this point for all browsers
  if (s.length < 24) {
    // Spidermonkey gets much slower when s.length >= 24 (on 64 bit archs)
    for (var i = 0; i < s.length; i++) if (s.charCodeAt(i) > 127) return false;
    return true;
  } else
    return !/[^\x00-\x7f]/.test(s);
}

//Provides: caml_bytes_unsafe_get mutable
function caml_bytes_unsafe_get (s, i) {
  return s.a[i] | 0;
}

//Provides: caml_bytes_unsafe_set
function caml_bytes_unsafe_set (s, i, c) {
  // The OCaml compiler uses Char.unsafe_chr on integers larger than 255!
  c &= 0xff;
  s.a[i] = c;
  return 0;
}

//Provides: caml_string_bound_error
//Requires: caml_invalid_argument
function caml_string_bound_error () {
  caml_invalid_argument ("index out of bounds");
}

//Provides: caml_bytes_bound_error
//Requires: caml_invalid_argument
function caml_bytes_bound_error () {
  caml_invalid_argument ("index out of bounds");
}

//Provides: caml_string_get
//Requires: caml_string_bound_error, caml_string_unsafe_get
//Requires: caml_ml_string_length
function caml_string_get (s, i) {
  if (i >>> 0 >= caml_ml_string_length(s)) caml_string_bound_error();
  return caml_string_unsafe_get (s, i);
}

//Provides: caml_string_get16
//Requires: caml_string_unsafe_get, caml_string_bound_error
//Requires: caml_ml_string_length
function caml_string_get16(s,i) {
  if (i >>> 0 >= caml_ml_string_length(s) - 1) caml_string_bound_error();
  var b1 = caml_string_unsafe_get (s, i),
      b2 = caml_string_unsafe_get (s, i + 1);
  return (b2 << 8 | b1);
}

//Provides: caml_bytes_get16
//Requires: caml_bytes_unsafe_get, caml_bytes_bound_error
function caml_bytes_get16(s,i) {
  if (i >>> 0 >= s.a.length - 1) caml_bytes_bound_error();
  var b1 = caml_bytes_unsafe_get (s, i),
      b2 = caml_bytes_unsafe_get (s, i + 1);
  return (b2 << 8 | b1);
}

//Provides: caml_string_get32
//Requires: caml_string_unsafe_get, caml_string_bound_error
//Requires: caml_ml_string_length
function caml_string_get32(s,i) {
  if (i >>> 0 >= caml_ml_string_length(s) - 3) caml_string_bound_error();
  var b1 = caml_string_unsafe_get (s, i),
      b2 = caml_string_unsafe_get (s, i + 1),
      b3 = caml_string_unsafe_get (s, i + 2),
      b4 = caml_string_unsafe_get (s, i + 3);
  return (b4 << 24 | b3 << 16 | b2 << 8 | b1);
}

//Provides: caml_bytes_get32
//Requires: caml_bytes_unsafe_get, caml_bytes_bound_error
function caml_bytes_get32(s,i) {
  if (i >>> 0 >= s.a.length - 3) caml_bytes_bound_error();
  var b1 = caml_bytes_unsafe_get (s, i),
      b2 = caml_bytes_unsafe_get (s, i + 1),
      b3 = caml_bytes_unsafe_get (s, i + 2),
      b4 = caml_bytes_unsafe_get (s, i + 3);
  return (b4 << 24 | b3 << 16 | b2 << 8 | b1);
}

//Provides: caml_string_get64
//Requires: caml_string_unsafe_get, caml_string_bound_error
//Requires: caml_int64_of_bytes
//Requires: caml_ml_string_length
function caml_string_get64(s,i) {
  if (i >>> 0 >= caml_ml_string_length(s) - 7) caml_string_bound_error();
  var a = new Array(8);
  for(var j = 0; j < 8; j++){
    a[7 - j] = caml_string_unsafe_get (s, i + j);
  }
  return caml_int64_of_bytes(a);
}

//Provides: caml_bytes_get64
//Requires: caml_bytes_unsafe_get, caml_bytes_bound_error
//Requires: caml_int64_of_bytes
function caml_bytes_get64(s,i) {
  if (i >>> 0 >= s.a.length- 7) caml_bytes_bound_error();
  var a = new Array(8);
  for(var j = 0; j < 8; j++){
    a[7 - j] = caml_bytes_unsafe_get (s, i + j);
  }
  return caml_int64_of_bytes(a);
}

//Provides: caml_bytes_get
//Requires: caml_bytes_bound_error, caml_bytes_unsafe_get
function caml_bytes_get (s, i) {
  if (i >>> 0 >= s.a.length) caml_bytes_bound_error();
  return caml_bytes_unsafe_get (s, i);
}

//Provides: caml_string_set
//Requires: caml_failwith
//If: js-string
function caml_string_set (s, i, c) {
  caml_failwith("caml_string_set");
}

//Provides: caml_string_set
//Requires: caml_string_unsafe_set, caml_string_bound_error
//If: !js-string
function caml_string_set (s, i, c) {
  if (i >>> 0 >= s.a.length) caml_string_bound_error();
  return caml_string_unsafe_set (s, i, c);
}

//Provides: caml_bytes_set16
//Requires: caml_bytes_bound_error, caml_bytes_unsafe_set
function caml_bytes_set16(s,i,i16){
  if (i >>> 0 >= s.a.length - 1) caml_bytes_bound_error();
  var b2 = 0xFF & i16 >> 8,
      b1 = 0xFF & i16;
  caml_bytes_unsafe_set (s, i + 0, b1);
  caml_bytes_unsafe_set (s, i + 1, b2);
  return 0
}

//Provides: caml_string_set16
//Requires: caml_failwith
//If: js-string
function caml_string_set16(s,i,i16){
  caml_failwith("caml_string_set16");
}

//Provides: caml_string_set16
//Requires: caml_bytes_set16
//If: !js-string
function caml_string_set16(s,i,i16){
  return caml_bytes_set16(s,i,i16);
}

//Provides: caml_bytes_set32
//Requires: caml_bytes_bound_error, caml_bytes_unsafe_set
function caml_bytes_set32(s,i,i32){
  if (i >>> 0 >= s.a.length - 3) caml_bytes_bound_error();
  var b4 = 0xFF & i32 >> 24,
      b3 = 0xFF & i32 >> 16,
      b2 = 0xFF & i32 >> 8,
      b1 = 0xFF & i32;
  caml_bytes_unsafe_set (s, i + 0, b1);
  caml_bytes_unsafe_set (s, i + 1, b2);
  caml_bytes_unsafe_set (s, i + 2, b3);
  caml_bytes_unsafe_set (s, i + 3, b4);
  return 0
}

//Provides: caml_string_set32
//Requires: caml_failwith
//If: js-string
function caml_string_set32(s,i,i32){
  caml_failwith("caml_string_set32");
}

//Provides: caml_string_set32
//Requires: caml_bytes_set32
//If: !js-string
function caml_string_set32(s,i,i32){
  return caml_bytes_set32(s,i,i32);
}

//Provides: caml_bytes_set64
//Requires: caml_bytes_bound_error, caml_bytes_unsafe_set
//Requires: caml_int64_to_bytes
function caml_bytes_set64(s,i,i64){
  if (i >>> 0 >= s.a.length - 7) caml_bytes_bound_error();
  var a = caml_int64_to_bytes(i64);
  for(var j = 0; j < 8; j++) {
    caml_bytes_unsafe_set (s, i + 7 - j, a[j]);
  }
  return 0
}

//Provides: caml_string_set64
//Requires: caml_failwith
//If: js-string
function caml_string_set64(s,i,i64){
  caml_failwith("caml_string_set64");
}

//Provides: caml_string_set64
//Requires: caml_bytes_set64
//If: !js-string
function caml_string_set64(s,i,i64){
  return caml_bytes_set64(s,i,i64);
}

//Provides: caml_bytes_set
//Requires: caml_bytes_bound_error, caml_bytes_unsafe_set
function caml_bytes_set (s, i, c) {
  if (i >>> 0 >= s.a.length) caml_bytes_bound_error();
  return caml_bytes_unsafe_set (s, i, c);
}

//Provides: caml_bytes_of_utf16_jsstring
//Requires: jsoo_is_ascii, caml_utf8_of_utf16, MlBytes, caml_jsbytes_to_array
function caml_bytes_of_utf16_jsstring (s) {
  if (!jsoo_is_ascii(s)); s = caml_utf8_of_utf16(s);
  return new MlBytes(caml_jsbytes_to_array(s));
}


//Provides: MlBytes
//Requires: jsoo_is_ascii, caml_utf16_of_utf8, caml_subarray_to_jsbytes
function MlBytes (a) {
  this.a = a;
}
MlBytes.prototype.toString = function(){
  return caml_subarray_to_jsbytes (this.a, 0, this.a.length);
};
MlBytes.prototype.toUtf16 = function (){
  var r = this.toString();
  return caml_utf16_of_utf8(r);
}
MlBytes.prototype.slice = function (){
  var content = this.a.slice();
  return new MlBytes(content);
}

//Provides: caml_uint8_array_of_bytes mutable
function caml_uint8_array_of_bytes (s) {
  return s.a;
}

//Provides: caml_uint8_array_of_string
//Requires: caml_ml_string_length, caml_string_unsafe_get
function caml_uint8_array_of_string (s) {
  var l = caml_ml_string_length(s);
  var a = new Array(l);
  var i = 0;
  for (; i < l; i++) a[i] = caml_string_unsafe_get(s,i);
  return a;
}

//Provides: caml_create_string const
//Requires: MlBytes, caml_invalid_argument
//If: !js-string
function caml_create_string(len) {
  if(len < 0) caml_invalid_argument("String.create");
  return new MlBytes(new globalThis.Uint8Array(len));
}
//Provides: caml_create_string const
//Requires: caml_invalid_argument
//If: js-string
function caml_create_string(len) {
  caml_invalid_argument("String.create");
}

//Provides: caml_create_bytes const
//Requires: MlBytes,caml_invalid_argument
function caml_create_bytes(len) {
  if (len < 0) caml_invalid_argument("Bytes.create");
  return new MlBytes(new globalThis.Uint8Array(len))
}

//Provides: caml_string_of_array
//Requires: caml_subarray_to_jsbytes, caml_string_of_jsbytes
function caml_string_of_array (a) {
  return caml_string_of_jsbytes(caml_subarray_to_jsbytes(a,0,a.length));
}

//Provides: caml_bytes_of_array
//Requires: MlBytes
function caml_bytes_of_array (a) {
  return new MlBytes(a);
}

//Provides: caml_compare_array
function caml_compare_array(a,b){
  var i;
  for(i = 0; i < Math.min(a.length,b.length); i++){
    if(a[i] < b[i]) return -1
    if(b[i] < a[i]) return 1
  }
  if(a.length < b.length) return -1
  if(b.length < a.length) return 1
  return 0
}

//Provides: caml_bytes_compare mutable
//Requires: caml_compare_array
function caml_bytes_compare(s1, s2) {
  return caml_compare_array(s1.a, s2.a);
}

//Provides: caml_bytes_equal mutable (const, const)
//Requires: caml_compare_array
function caml_bytes_equal(s1, s2) {
  if(s1 === s2) return 1;
  return (caml_compare_array(s1.a, s2.a) === 0)?1:0;
}

//Provides: caml_string_notequal mutable (const, const)
//Requires: caml_string_equal
function caml_string_notequal(s1, s2) { return 1-caml_string_equal(s1, s2); }

//Provides: caml_bytes_notequal mutable (const, const)
//Requires: caml_bytes_equal
function caml_bytes_notequal(s1, s2) { return 1-caml_bytes_equal(s1, s2); }

//Provides: caml_bytes_lessequal mutable
//Requires: caml_compare_array
function caml_bytes_lessequal(s1, s2) {
  return (caml_compare_array(s1.a, s2.a) <= 0)?1:0;
}

//Provides: caml_bytes_lessthan mutable
//Requires: caml_compare_array
function caml_bytes_lessthan(s1, s2) {
  return (caml_compare_array(s1.a, s2.a) < 0)?1:0;
}

//Provides: caml_string_greaterequal
//Requires: caml_string_lessequal
function caml_string_greaterequal(s1, s2) {
  return caml_string_lessequal(s2,s1);
}
//Provides: caml_bytes_greaterequal
//Requires: caml_bytes_lessequal
function caml_bytes_greaterequal(s1, s2) {
  return caml_bytes_lessequal(s2,s1);
}

//Provides: caml_string_greaterthan
//Requires: caml_string_lessthan
function caml_string_greaterthan(s1, s2) {
  return caml_string_lessthan(s2, s1);
}

//Provides: caml_bytes_greaterthan
//Requires: caml_bytes_lessthan
function caml_bytes_greaterthan(s1, s2) {
  return caml_bytes_lessthan(s2, s1);
}

//Provides: caml_fill_bytes
function caml_fill_bytes(s, i, l, c) {
  if (l > 0) {
    for (l += i; i < l; i++) s.a[i] = c;
  }
  return 0;
}

//Provides: caml_blit_bytes
//Requires: caml_subarray_to_jsbytes
function caml_blit_bytes(s1, i1, s2, i2, len) {
  if (len == 0) return 0;
  var c1 = s1.a;
  var c2 = s2.a;
  if (i2 <= i1) {
    for (var i = 0; i < len; i++) c2 [i2 + i] = c1 [i1 + i];
  } else {
    for (var i = len - 1; i >= 0; i--) c2 [i2 + i] = c1 [i1 + i];
  }
  return 0;
}

//Provides: caml_blit_string
//Requires: caml_blit_bytes, caml_bytes_of_string
function caml_blit_string(a,b,c,d,e) {
  caml_blit_bytes(caml_bytes_of_string(a),b,c,d,e);
  return 0
}

//Provides: caml_ml_bytes_length const
function caml_ml_bytes_length(s) { return s.a.length }

//Provides: caml_string_unsafe_get const
//If: js-string
function caml_string_unsafe_get (s, i) {
  return s.charCodeAt(i);
}

//Provides: caml_string_unsafe_set
//Requires: caml_failwith
//If: js-string
function caml_string_unsafe_set (s, i, c) {
  caml_failwith("caml_string_unsafe_set");
}

//Provides: caml_ml_string_length const
//If: js-string
function caml_ml_string_length(s) {
  return s.length
}

//Provides: caml_string_compare const
//If: js-string
function caml_string_compare(s1, s2) {
  return (s1 < s2)?-1:(s1 > s2)?1:0;
}

//Provides: caml_string_equal const
//If: js-string
function caml_string_equal(s1, s2) {
  if(s1 === s2) return 1;
  return 0;
}

//Provides: caml_string_lessequal const
//If: js-string
function caml_string_lessequal(s1, s2) {
  return (s1 <= s2)?1:0;
}

//Provides: caml_string_lessthan const
//If: js-string
function caml_string_lessthan(s1, s2) {
  return (s1 < s2)?1:0;
}

//Provides: caml_string_of_bytes
//Requires: caml_string_of_jsbytes, caml_string_of_array
//If: js-string
function caml_string_of_bytes(s) {
  return caml_string_of_array(s.a);
}

//Provides: caml_bytes_of_string const
//Requires: caml_bytes_of_jsbytes, caml_jsbytes_of_string
//If: js-string
function caml_bytes_of_string(s) {
  return caml_bytes_of_jsbytes(caml_jsbytes_of_string(s));
}

//Provides: caml_string_of_jsbytes const
//If: js-string
function caml_string_of_jsbytes(x) { return x }

//Provides: caml_jsbytes_of_string const
//If: js-string
function caml_jsbytes_of_string(x) { return x }

//Provides: caml_jsstring_of_string const
//Requires: jsoo_is_ascii, caml_utf16_of_utf8
//If: js-string
function caml_jsstring_of_string(s) {
  if(jsoo_is_ascii(s))
    return s;
  return caml_utf16_of_utf8(s); }

//Provides: caml_string_of_jsstring const
//Requires: jsoo_is_ascii, caml_utf8_of_utf16, caml_string_of_jsbytes
//If: js-string
function caml_string_of_jsstring (s) {
  if (jsoo_is_ascii(s))
    return caml_string_of_jsbytes(s)
  else return caml_string_of_jsbytes(caml_utf8_of_utf16(s));
}

//Provides: caml_bytes_of_jsbytes const
//Requires: MlBytes, caml_jsbytes_to_array
function caml_bytes_of_jsbytes(s) { return new MlBytes(caml_jsbytes_to_array(s)); }


// The section below should be used when use-js-string=false

//Provides: caml_string_unsafe_get const
//Requires: caml_bytes_unsafe_get
//If: !js-string
function caml_string_unsafe_get (s, i) {
  return caml_bytes_unsafe_get(s,i);
}

//Provides: caml_string_unsafe_set
//Requires: caml_bytes_unsafe_set
//If: !js-string
function caml_string_unsafe_set (s, i, c) {
  return caml_bytes_unsafe_set(s,i,c);
}

//Provides: caml_ml_string_length const
//Requires: caml_ml_bytes_length
//If: !js-string
function caml_ml_string_length(s) {
  return caml_ml_bytes_length(s)
}

//Provides: caml_string_compare
//Requires: caml_bytes_compare
//If: !js-string
function caml_string_compare(s1, s2) {
  return caml_bytes_compare(s1,s2)
}

//Provides: caml_string_equal
//Requires: caml_bytes_equal
//If: !js-string
function caml_string_equal(s1, s2) {
  return caml_bytes_equal(s1,s2)
}

//Provides: caml_string_lessequal
//Requires: caml_bytes_lessequal
//If: !js-string
function caml_string_lessequal(s1, s2) {
  return caml_bytes_lessequal(s1,s2)
}

//Provides: caml_string_lessthan
//Requires: caml_bytes_lessthan
//If: !js-string
function caml_string_lessthan(s1, s2) {
  return caml_bytes_lessthan(s1,s2)
}

//Provides: caml_string_of_bytes
//If: !js-string
function caml_string_of_bytes(s) { return s }

//Provides: caml_bytes_of_string const
//If: !js-string
function caml_bytes_of_string(s) { return s }

//Provides: caml_string_of_jsbytes const
//Requires: caml_bytes_of_jsbytes
//If: !js-string
function caml_string_of_jsbytes(s) { return caml_bytes_of_jsbytes(s); }

//Provides: caml_jsbytes_of_string const
//Requires: caml_subarray_to_jsbytes
//If: !js-string
function caml_jsbytes_of_string(s) {
  return caml_subarray_to_jsbytes(s.a, 0, s.a.length);
}

//Provides: caml_jsstring_of_string mutable (const)
//If: !js-string
function caml_jsstring_of_string(s){
  return s.toUtf16()
}

//Provides: caml_string_of_jsstring
//Requires: caml_bytes_of_utf16_jsstring
//If: !js-string
function caml_string_of_jsstring (s) {
  return caml_bytes_of_utf16_jsstring(s);
}

//Provides: caml_is_ml_bytes
//Requires: MlBytes
function caml_is_ml_bytes(s) {
  return (s instanceof MlBytes);
}

//Provides: caml_ml_bytes_content
function caml_ml_bytes_content(s) {
  return s.a
}

//Provides: caml_is_ml_string
//Requires: jsoo_is_ascii
//If: js-string
function caml_is_ml_string(s) {
  return (typeof s === "string" && !/[^\x00-\xff]/.test(s));
}

//Provides: caml_is_ml_string
//Requires: caml_is_ml_bytes
//If: !js-string
function caml_is_ml_string(s) {
  return caml_is_ml_bytes(s);
}

// The functions below are deprecated

//Provides: caml_js_to_byte_string const
//Requires: caml_string_of_jsbytes
function caml_js_to_byte_string(s) { return caml_string_of_jsbytes(s) }

//Provides: caml_new_string
//Requires: caml_string_of_jsbytes
function caml_new_string (s) { return caml_string_of_jsbytes(s) }

//Provides: caml_js_from_string mutable (const)
//Requires: caml_jsstring_of_string
function caml_js_from_string(s) {
  return caml_jsstring_of_string(s)
}

//Provides: caml_to_js_string mutable (const)
//Requires: caml_jsstring_of_string
function caml_to_js_string(s) {
  return caml_jsstring_of_string(s)
}

//Provides: caml_js_to_string const
//Requires: caml_string_of_jsstring
function caml_js_to_string (s) {
  return caml_string_of_jsstring(s);
}


//Provides: caml_array_of_string
//Requires: caml_uint8_array_of_string
function caml_array_of_string(x) { return caml_uint8_array_of_string(x) }

//Provides: caml_array_of_bytes
//Requires: caml_uint8_array_of_bytes
function caml_array_of_bytes(x) { return caml_uint8_array_of_bytes(x) }

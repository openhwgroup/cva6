/*
 * Pseudo JSON parser
 *
 * Copyright (c) 2017 Fabrice Bellard
 * Copyright (C) 2018,2019, Esperanto Technologies Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License")
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * THIS FILE IS BASED ON THE RISCVEMU SOURCE CODE WHICH IS DISTRIBUTED
 * UNDER THE FOLLOWING LICENSE:
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <inttypes.h>
#include <assert.h>
#include <fcntl.h>
#include <errno.h>
#include <unistd.h>
#include <time.h>
#include <ctype.h>

#include "cutils.h"
#include "json.h"
#include "fs_utils.h"

static JSONValue parse_string(const char **pp)
{
    char buf[4096], *q;
    const char *p;
    int c, h;

    q = buf;
    p = *pp;
    p++;
    for (;;) {
        c = *p++;
        if (c == '\0' || c == '\n') {
            return json_error_new("unterminated string");
        } else if (c == '\"') {
            break;
            } else if (c == '\\') {
                c = *p++;
                switch (c) {
                case '\'':
                case '\"':
                case '\\':
                    goto add_char;
                case 'n':
                    c = '\n';
                    goto add_char;
                case 'r':
                    c = '\r';
                    goto add_char;
                case 't':
                    c = '\t';
                    goto add_char;
                case 'x':
                    h = from_hex(*p++);
                    if (h < 0)
                        return json_error_new("invalid hex digit");
                    c = h << 4;
                    h = from_hex(*p++);
                    if (h < 0)
                        return json_error_new("invalid hex digit");
                    c |= h;
                    goto add_char;
                default:
                    return json_error_new("unknown escape code");
                }
            } else {
            add_char:
            if (q >= buf + sizeof(buf) - 1)
                return json_error_new("string too long");
            *q++ = c;
        }
    }
    *q = '\0';
    *pp = p;
    return json_string_new(buf);
}

static JSONProperty *json_object_get2(JSONObject *obj, const char *name)
{
    JSONProperty *f;
    int i;
    for (i = 0; i < obj->len; i++) {
        f = &obj->props[i];
        if (!strcmp(f->name.u.str->data, name))
            return f;
    }
    return NULL;
}

JSONValue json_object_get(JSONValue val, const char *name)
{
    JSONProperty *f;
    JSONObject *obj;

    if (val.type != JSON_OBJ)
        return json_undefined_new();
    obj = val.u.obj;
    f = json_object_get2(obj, name);
    if (!f)
        return json_undefined_new();
    return f->value;
}

int json_object_set(JSONValue val, const char *name, JSONValue prop_val)
{
    JSONObject *obj;
    JSONProperty *f;
    int new_size;

    if (val.type != JSON_OBJ)
        return -1;
    obj = val.u.obj;
    f = json_object_get2(obj, name);
    if (f) {
        json_free(f->value);
        f->value = prop_val;
    } else {
        if (obj->len >= obj->size) {
            new_size = max_int(obj->len + 1, obj->size * 3 / 2);
            obj->props = (JSONProperty *)realloc(obj->props, new_size * sizeof(JSONProperty));
            obj->size = new_size;
        }
        f = &obj->props[obj->len++];
        f->name = json_string_new(name);
        f->value = prop_val;
    }
    return 0;
}

JSONValue json_array_get(JSONValue val, int idx)
{
    JSONArray *array;

    if (val.type != JSON_ARRAY)
        return json_undefined_new();
    array = val.u.array;
    if (idx < array->len) {
        return array->tab[idx];
    } else {
        return json_undefined_new();
    }
}

int json_array_set(JSONValue val, int idx, JSONValue prop_val)
{
    JSONArray *array;
    int new_size;

    if (val.type != JSON_ARRAY)
        return -1;
    array = val.u.array;
    if (idx < array->len) {
        json_free(array->tab[idx]);
        array->tab[idx] = prop_val;
    } else if (idx == array->len) {
        if (array->len >= array->size) {
            new_size = max_int(array->len + 1, array->size * 3 / 2);
            array->tab = (JSONValue *)realloc(array->tab, new_size * sizeof(JSONValue));
            array->size = new_size;
        }
        array->tab[array->len++] = prop_val;
    } else {
        return -1;
    }
    return 0;
}

const char *json_get_str(JSONValue val)
{
    if (val.type != JSON_STR)
        return NULL;
    return val.u.str->data;
}

const char *json_get_error(JSONValue val)
{
    if (val.type != JSON_EXCEPTION)
        return NULL;
    return val.u.str->data;
}

JSONValue json_string_new2(const char *str, int len)
{
    JSONString *str1 = (JSONString *)malloc(sizeof(JSONString) + len + 1);

    str1->len = len;
    memcpy(str1->data, str, len + 1);

    JSONValue val;
    val.type = JSON_STR;
    val.u.str = str1;
    return val;
}

JSONValue json_string_new(const char *str)
{
    return json_string_new2(str, strlen(str));
}

JSONValue __attribute__((format(printf, 1, 2))) json_error_new(const char *fmt, ...)
{
    JSONValue val;
    va_list ap;
    char buf[256];

    va_start(ap, fmt);
    vsnprintf(buf, sizeof(buf), fmt, ap);
    va_end(ap);
    val = json_string_new(buf);
    val.type = JSON_EXCEPTION;
    return val;
}

JSONValue json_object_new(void)
{
    JSONObject *obj = (JSONObject *)mallocz(sizeof(JSONObject));

    JSONValue val;
    val.type = JSON_OBJ;
    val.u.obj = obj;
    return val;
}

JSONValue json_array_new(void)
{
    JSONArray *array = (JSONArray *)mallocz(sizeof(JSONArray));

    JSONValue val;
    val.type = JSON_ARRAY;
    val.u.array = array;
    return val;
}

void json_free(JSONValue val)
{
    switch (val.type) {
    case JSON_STR:
    case JSON_EXCEPTION:
        free(val.u.str);
        break;
    case JSON_INT:
    case JSON_BOOL:
    case JSON_NULL:
    case JSON_UNDEFINED:
        break;
    case JSON_ARRAY:
        {
            JSONArray *array = val.u.array;
            int i;

            for (i = 0; i < array->len; i++) {
                json_free(array->tab[i]);
            }
            free(array);
        }
        break;
    case JSON_OBJ:
        {
            JSONObject *obj = val.u.obj;
            JSONProperty *f;
            int i;

            for (i = 0; i < obj->len; i++) {
                f = &obj->props[i];
                json_free(f->name);
                json_free(f->value);
            }
            free(obj);
        }
        break;
    default:
        abort();
    }
}

static void skip_spaces(const char **pp)
{
    const char *p;
    p = *pp;
    for (;;) {
        if (isspace(*p)) {
            p++;
        } else if (p[0] == '/' && p[1] == '/') {
            p += 2;
            while (*p != '\0' && *p != '\n')
                p++;
        } else if (p[0] == '/' && p[1] == '*') {
            p += 2;
            while (*p != '\0' && (p[0] != '*' || p[1] != '/'))
                p++;
            if (*p != '\0')
                p += 2;
        } else {
            break;
        }
    }
    *pp = p;
}

static inline BOOL is_ident_first(int c)
{
    return (c >= 'a' && c <= 'z') ||
        (c >= 'A' && c <= 'Z') ||
        c == '_' || c == '$';
}

static int parse_ident(char *buf, int buf_size, const char **pp)
{
    char *q;
    const char *p;
    p = *pp;
    q = buf;
    *q++ = *p++; /* first char is already tested */
    while (is_ident_first(*p) || isdigit(*p)) {
        if ((q - buf) >= buf_size - 1)
            return -1;
        *q++ = *p++;
    }
    *pp = p;
    *q = '\0';
    return 0;
}

JSONValue json_parse_value2(const char **pp)
{
    char buf[128];
    const char *p;
    JSONValue val, val1, tag;

    p = *pp;
    skip_spaces(&p);
    if (*p == '\0') {
        return json_error_new("unexpected end of file");
    }
    if (*p == '0' && p[1] == 'x') {
        p += 2;
        val = json_int64_new(strtoll(p, (char **)&p, 16));
    } else if (isdigit(*p)) {
        val = json_int64_new(strtoll(p, (char **)&p, 0));
    } else if (*p == '"') {
        val = parse_string(&p);
    } else if (*p == '{') {
        p++;
        val = json_object_new();
        for (;;) {
            skip_spaces(&p);
            if (*p == '}') {
                p++;
                break;
            }
            if (*p == '"') {
                tag = parse_string(&p);
                if (json_is_error(tag))
                    return tag;
            } else if (is_ident_first(*p)) {
                if (parse_ident(buf, sizeof(buf), &p) < 0)
                    goto invalid_prop;
                tag = json_string_new(buf);
            } else {
                goto invalid_prop;
            }
            //            fprintf(dromajo_stdout, "property: %s\n", json_get_str(tag));
            if (tag.u.str->len == 0) {
            invalid_prop:
                return json_error_new("Invalid property name");
            }
            skip_spaces(&p);
            if (*p != ':') {
                return json_error_new("':' expected");
            }
            p++;

            val1 = json_parse_value2(&p);
            json_object_set(val, tag.u.str->data, val1);

            skip_spaces(&p);
            if (*p == ',') {
                p++;
            } else if (*p != '}') {
                return json_error_new("expecting ',' or '}'");
            }
        }
    } else if (*p == '[') {
        int idx;

        p++;
        val = json_array_new();
        idx = 0;
        for (;;) {
            skip_spaces(&p);
            if (*p == ']') {
                p++;
                break;
            }
            val1 = json_parse_value2(&p);
            json_array_set(val, idx++, val1);

            skip_spaces(&p);
            if (*p == ',') {
                p++;
            } else if (*p != ']') {
                return json_error_new("expecting ',' or ']'");
            }
        }
    } else if (is_ident_first(*p)) {
        if (parse_ident(buf, sizeof(buf), &p) < 0)
            goto unknown_id;
        if (!strcmp(buf, "null")) {
            val = json_null_new();
        } else if (!strcmp(buf, "true")) {
            val = json_bool_new(TRUE);
        } else if (!strcmp(buf, "false")) {
            val = json_bool_new(FALSE);
        } else {
        unknown_id:
            return json_error_new("unknown identifier: '%s'", buf);
        }
    } else {
        return json_error_new("unexpected character");
    }
    *pp = p;
    return val;
}

JSONValue json_parse_value(const char *p)
{
    JSONValue val;
    val = json_parse_value2(&p);
    if (json_is_error(val))
        return val;
    skip_spaces(&p);
    if (*p != '\0') {
        json_free(val);
        return json_error_new("unexpected characters at the end");
    }
    return val;
}

JSONValue json_parse_value_len(const char *p, int len)
{
    char *str = (char *)malloc(len + 1);
    memcpy(str, p, len);
    str[len] = '\0';

    JSONValue val = json_parse_value(str);
    free(str);

    return val;
}

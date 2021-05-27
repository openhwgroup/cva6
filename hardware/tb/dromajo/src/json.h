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
#ifndef JSON_H
#define JSON_H

#include <stdint.h>

#include "cutils.h"

typedef enum {
    JSON_STR,
    JSON_INT,
    JSON_OBJ,
    JSON_ARRAY,
    JSON_BOOL,
    JSON_NULL,
    JSON_UNDEFINED,
    JSON_EXCEPTION,
} JSONTypeEnum;

typedef struct {
    int len;
    char data[0];
} JSONString;

typedef struct JSONValue {
    JSONTypeEnum type;
    union {
        JSONString *str;
        int64_t int64;
        BOOL b;
        struct JSONObject *obj;
        struct JSONArray *array;
    } u;
} JSONValue;

typedef struct JSONProperty {
    JSONValue name;
    JSONValue value;
} JSONProperty;

typedef struct JSONObject {
    int len;
    int size;
    JSONProperty *props;
} JSONObject;

typedef struct JSONArray {
    int len;
    int size;
    JSONValue *tab;
} JSONArray;

JSONValue json_string_new2(const char *str, int len);
JSONValue json_string_new(const char *str);
JSONValue __attribute__((format(printf, 1, 2))) json_error_new(const char *fmt, ...);
void json_free(JSONValue val);

JSONValue json_object_new(void);
JSONValue json_object_get(JSONValue val, const char *name);
int json_object_set(JSONValue val, const char *name, JSONValue prop_val);

JSONValue json_array_new(void);
JSONValue json_array_get(JSONValue val, int idx);
int json_array_set(JSONValue val, int idx, JSONValue prop_val);

static inline BOOL json_is_error(JSONValue val)
{
    return val.type == JSON_EXCEPTION;
}

static inline BOOL json_is_undefined(JSONValue val)
{
    return val.type == JSON_UNDEFINED;
}

static inline JSONValue json_undefined_new(void)
{
    JSONValue val;
    val.type = JSON_UNDEFINED;
    val.u.int64 = 0;
    return val;
}

static inline JSONValue json_null_new(void)
{
    JSONValue val;
    val.type = JSON_NULL;
    val.u.int64 = 0;
    return val;
}

static inline JSONValue json_int64_new(int64_t v)
{
    JSONValue val;
    val.type = JSON_INT;
    val.u.int64 = v;
    return val;
}

static inline JSONValue json_bool_new(BOOL v)
{
    JSONValue val;
    val.type = JSON_BOOL;
    val.u.b = v;
    return val;
}

const char *json_get_str(JSONValue val);
const char *json_get_error(JSONValue val);

JSONValue json_parse_value(const char *p);
JSONValue json_parse_value_len(const char *p, int len);

#endif /* JSON_H */

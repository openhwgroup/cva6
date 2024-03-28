# Copyright 2024 Thales DIS France SAS
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# Original Author: Zbigniew CHAMSKI - Thales

from lark import Lark

# Simple ad-hoc grammar for parsing config packages of CVA6

config_pkg_parser = Lark("""
    package : "package" ident ";" localparam* "endpackage"

    value : "'" "{" (field ",")* field "}"
          | simple_value

    simple_value : ident
                 | sv_int

    ident: (namespace "::")? IDENT

    namespace: IDENT

    sv_int : UNSIGNED
           | EXPL_WIDTH_BIN
           | EXPL_WIDTH_OCT
           | EXPL_WIDTH_DEC
           | EXPL_WIDTH_HEX

    UNSIGNED:       /[0-9]+/
    EXPL_WIDTH_BIN: /[0-9]+'b[0-1_]+/
    EXPL_WIDTH_OCT: /[0-9]+'o[0-7_]+/
    EXPL_WIDTH_DEC: /[0-9]+'d[0-9_]+/
    EXPL_WIDTH_HEX: /[0-9]+'h[0-9a-fA-F_]+/
    IDENT:          /[A-Za-z_][A-Za-z_0-9]*/
    BIT_T:          "bit"
    UNSIGNED_T:     "unsigned"

    sv_type : BIT_T
	    | UNSIGNED_T

    user_type : ident

    field : ident ":" field_value

    field_value : complex_value
                | simple_value

    complex_value : sv_type "'" "(" simple_value ")"
                  | width "'" "(" struct_init ")"
                  | "{" repeat struct_init "}"

    struct_init : "{" (sv_int ",")* sv_int "}"

    localparam : "localparam" [user_type] ident "=" value ";"

    width : UNSIGNED
    repeat: UNSIGNED

    COMMENT: /\/\/.*/
    %ignore COMMENT
    %import common.UNSIGNED_NUMBER -> INTEGER
    %import common.WS
    %ignore WS

""", start='package')

# Example usage:
#
# with open('../../core/include/cv32a65x_config_pkg.sv', 'r') as f:
#     text = '\n'.join(f.readlines())
#
# print(config_pkg_parser.parse(text).pretty())



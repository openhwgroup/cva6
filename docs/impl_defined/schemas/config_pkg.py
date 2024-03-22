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

# Schema of a config package file

from dataclasses import dataclass
from typing import List, Union, Optional

# Enumerate config struct fields
@dataclass
class CfgStructFieldName(Enum):
    NrCommitPorts: "NrCommitPorts"
    AxiAddrWidth: "AxiAddrWidth"
    AxiDataWidth: "AxiDataWidth"
    AxiIdWidth: "AxiIdWidth"
    AxiUserWidth: "AxiUserWidth"
    NrLoadBufEntries: "NrLoadBufEntries"
    FpuEn: "FpuEn"
    XF16: "XF16"
    XF16ALT: "XF16ALT"
    XF8: "XF8"
    RVA: "RVA"
    RVB: "RVB"
    RVV: "RVV"
    RVC: "RVC"
    RVZCB: "RVZCB"
    XFVec: "XFVec"
    CvxifEn: "CvxifEn"
    ZiCondExtEn: "ZiCondExtEn"
    RVF: "RVF"
    RVD: "RVD"
    FpPresent: "FpPresent"
    NSX: "NSX"
    FLen: "FLen"
    RVFVec: "RVFVec"
    XF16Vec: "XF16Vec"
    XF16ALTVec: "XF16ALTVec"
    XF8Vec: "XF8Vec"
    NrRgprPorts: "NrRgprPorts"
    NrWbPorts: "NrWbPorts"
    EnableAccelerator: "EnableAccelerator"
    RVS: "RVS"
    RVU: "RVU"
    HaltAddress: "HaltAddress"
    ExceptionAddress: "ExceptionAddress"
    RASDepth: "RASDepth"
    BTBEntries: "BTBEntries"
    BHTEntries: "BHTEntries"
    DmBaseAddress: "DmBaseAddress"
    TvalEn: "TvalEn"
    NrPMPEntries: "NrPMPEntries"
    PMPCfgRstVal: "PMPCfgRstVal"
    PMPAddrRstVal: "PMPAddrRstVal"
    PMPEntryReadOnly: "PMPEntryReadOnly"
    NOCType: "NOCType"
    NrNonIdempotentRules: "NrNonIdempotentRules"
    NonIdempotentAddrBase: "NonIdempotentAddrBase"
    NonIdempotentLength: "NonIdempotentLength"
    NrExecuteRegionRules: "NrExecuteRegionRules"
    ExecuteRegionAddrBase: "ExecuteRegionAddrBase"
    ExecuteRegionLength: "ExecuteRegionLength"
    NrCachedRegionRules: "NrCachedRegionRules"
    CachedRegionAddrBase: "CachedRegionAddrBase"
    CachedRegionLength: "CachedRegionLength"
    MaxOutstandingStores: "MaxOutstandingStores"
    DebugEn: "DebugEn"
    NonIdemPotenceEn: "NonIdemPotenceEn"
    AxiBurstWriteEn: "AxiBurstWriteEn"

# RTL localparam definition
@dataclass
class SvLocalParam:
    ident: str
    value: Union[int,str]
    type: Optional[str]

# CVA6 config struct field
@dataclass
class CfgStructField:
    ident: CfgStructFieldName
    sv_type: Optional[str]
    # The string can be either:
    # - an OmegaConf reference to a localparam value, or
    # - a string containing a localparam name.
    value: str

# Complete package config
@dataclass
class ConfigPkgCfgStruct:
    name: str
    params: List[SvLocalParam]
    fields: List[CfgStructField]

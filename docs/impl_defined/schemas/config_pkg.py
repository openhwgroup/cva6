#import variconf, dataclasses
from typing import Union, Optional

# RTL localparam definition
@dataclass SvLocalParam:
    ident: str
    value: Union[int,str]
    type: Optional[str]

# CVA6 config struct field
@dataclass CfgStructField:
    ident: str
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

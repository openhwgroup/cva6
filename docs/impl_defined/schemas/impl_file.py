# Schema of an Implementation-Defined Behaviors file

from dataclasses import dataclass
import variconf
from typing import List, Union, Optional

# Version control: repository location + revision
# Revision ('rev') must be a quoted string in Yaml file
# in order to prevent type conversion of date-like tags.
@dataclass
class RepoRev:
    repo: str      # Repository URL or path
    rev: str       # Rvision ID

# Complete configuration of referenced information.
# NOTE: 'config' designates a single RTL configuration
# that unequivocally fixes *ALL* implementation-defined
# behaviors.
@dataclass
class ImplConfig:
    config: str
    spec: RepoRev
    docs: RepoRev
    rtl: RepoRev
    spike: RepoRev

# Single specification sentence that leaves implementation freedom.
# The URL should ideally contain begin+end character positions (line+col).
# Positions could also be expresses as explicit model elements.
@dataclass
class SpecPoint:
    url: str
    normative: bool
    value_range: str
    spec_text: Optional[str] = None

# Choice made by the current implementation
@dataclass
class ImplChoice:
    value: str
    compliant: bool
    rationale: str

# Documentation support for a (relevant) spec point.
@dataclass
class DocSupport:
    addressed: bool
    correct: bool
    value: str
    spec_text: str
    userman_text: str
    ipxact_text: str
    comment: Optional[str] = None

# RTL support for a (relevant) spec point.
# It is assumed that an RTL config leaves no further impl-defined freedom.
@dataclass
class RtlSupport:
    addressed: bool
    correct: bool
    value: str
    comment: Optional[str] = None

# Setting for a single Spike parameter
@dataclass
class SpikeParamSetting:
    name: str
    value: Union[int, str]

# Spike configuration needed to achieve a specific value
# of an implementation-defined choice
@dataclass
class SpikeValueConfig:
    value: Union[int, str]
    param_config: List[SpikeParamSetting]

# List of possible values achievable with Spike
# for a given implementation choice.
@dataclass
class SpikeValues:
    default: Union[int, str]
    explicit: List[SpikeValueConfig]

# Spike support for a given implementation choice
@dataclass
class SpikeSupport:
    addressed: bool
    correct: bool
    parametric: bool
    values: SpikeValues
    comment: Optional[str] = None

# A single implementation-defined behavior allowed by the spec
@dataclass
class Behavior:
    tag: str
    spec: SpecPoint
    relevant: bool
    relevant_why: str
    impl_choice: Optional[ImplChoice] = None
    doc: Optional[DocSupport] = None
    rtl: Optional[RtlSupport] = None
    spike: Optional[SpikeSupport] = None
    comment: Optional[str] = None

# List of implementation-defined/-dependent behaviors according
# to the specification.
@dataclass
class ImplSpecificBehaviors:
    context: ImplConfig
    behaviors: List[Behavior]


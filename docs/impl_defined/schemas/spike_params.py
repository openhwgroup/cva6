from typing import Optional

# Structure for outputting Spike params
@dataclass
class SpikeParam:
    name: str
    value_type: str
    default: Any
    description: str

# Configuration of a core
@dataclass
class CoreConfig:
    # Id of the core
    core_id: int
    # Boot address
    boot_addr: int
    # List of extension names
    extensions: List[str]
    # ISA: FORNOW a string, could become a structured type
    isa: str
    # Architecture ID, should become an explicit enum based on RV site info.
    marchid: int
    # If true, enable writes into MISA register.
    misa_we: bool
    # If true, enable modifications of misa_we.
    misa_we_enable: bool
    # If 'true', support unaligned memory accesses.
    misaligned_memaccess: bool
    # MMU operation mode (could become an enum).
    mmu_mode: str
    # Vendor ID, should become an explicit enum based on RV site info.
    mvendorid: int
    # Base address of PMPADDR0 CSR
    pmpaddr0: int
    # Base address of PMPCFG0 CSR
    pmpcfg0: int
    # Number of PMP regions
    pmpregions: int
    # Set of supported operation modes (subset of { M, S, U })
    priv: str
    # Enable writing into *STATUS.FS
    status_fs_field_we: bool
    # Enable changing status_fs_field_we setting.
    status_fs_field_we_enable: bool
    # Enable writing into *STATUS.VS
    status_vs_field_we: bool
    # Enable changing status_fs_field_we setting.
    status_vs_field_we_enable: bool

@dataclass
class SpikeParamTree:
    bootrom: bool
    bootrom_base: int
    bootrom_size: int
    dram: bool
    dram_base: int
    dram_size: int
    generic_core_config: bool
    log_commits: bool
    max_steps: int
    max_steps_enabled: bool
    default_core_config: CoreConfig
    per_core_configs: List[CoreConfig]

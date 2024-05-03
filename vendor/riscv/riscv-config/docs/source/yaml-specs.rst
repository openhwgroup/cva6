###################
YAML Specifications
###################

This section provides details of the ISA and Platform spec YAML files that need to be provided by the user.

.. _isa_yaml_spec:

ISA YAML Spec
=============

.. note::
  
  All integer fields accept values as integers or hexadecimals (can be used interchangeably) unless specified otherwise.

  Different examples of the input yamls and the generated checked YAMLs can be found here : `Examples <https://github.com/riscv/riscv-config/tree/master/examples>`_

.. include:: schema_isa.rst
.. include:: schema_custom.rst

CSR Template
============
All csrs are defined using a common template. Two variants are available: csrs with subfields and
those without

CSRs with sub-fields
--------------------

.. code-block:: yaml

  <name>:                                   # name of the csr
    description: <text>                     # textual description of the csr
    address: <hex>                          # address of the csr
    priv_mode: <D/M/H/S/U>                  # privilege mode that owns the register
    reset-val: <hex>                        # Reset value of the register. This an accumulation 
                                            # of the all reset values of the sub-fields 
    rv32:                                   # this node and its subsequent fields can exist 
                                            # if [M/S/U]XL value can be 1
      accessible: <boolean>                 # indicates if the csr is accessible in rv32 mode or not. 
                                            # When False, all fields below will be trimmed off 
                                            # in the checked yaml. False also indicates that 
                                            # access-exception should be generated. 
      fields:                               # a quick summary of the list of all fields of the 
                                            # csr including a list of WPRI fields of the csr.
        - <field_name1>
        - <field_name2>
        - - [23,30]                         # A list which contains a squashed pair 
          - 6                               # (of form [lsb,msb]) of all WPRI bits within the 
                                            # csr. Does not exist if there are no WPRI bits
  
      <field_name1>:                        # name of the field
        description: <text>                 # textual description of the csr
        shadow: <csr-name>::<field>         # which this field shadows,'none' indicates that
                                            # this field does not shadow anything.
        shadow_type: <text>                 # indicates the type of shadowing used. Can be one of - 
                                            # rw or ro
        msb: <integer>                      # msb index of the field. max: 31, min:0
        lsb: <integer>                      # lsb index of the field. max: 31, min:0
        implemented: <boolean>              # indicates if the user has implemented this field 
                                            # or not. When False, all 
                                            # fields below this will be trimmed.
        type:                               # type of field. Can be only one of the following
          wlrl: [list of value-descriptors] # field is wlrl and the set of legal values.
          ro_constant: <hex>                # field is readonly and will return the same value.
          ro_variable: True                 # field is readonly but the value returned depends 
                                            # on other arch-states
          warl:                             # field is warl type. Refer to WARL section
            dependency_fields: [list]    
            legal: [list of warl-string]
            wr_illegal: [list of warl-string]           
    rv64:                                   # this node and its subsequent fields can exist 
                                            # if [M/S/U]XL value can be 2
      accessible: <boolean>                 # indicates if this register exists in rv64 mode 
                                            # or not. Same definition as for rv32 node.
    rv128:                                  # this node and its subsequent fields can exist if 
                                            # [M/S/U]XL value can be 3
      accessible: <boolean>                 # indicates if this register exists in rv128 mode 
                                            # or not. Same definition as for rv32 node.                          

See register `mstatus` for an example.

CSRs without sub-fields
-----------------------

.. code-block:: yaml

  <name>:                                 # name of the csr
    description: <text>                   # textual description of the csr
    address: <hex>                        # address of the csr
    priv_mode: <D/M/H/S/U>                # privilege mode that owns the register
    reset-val: <hex>                      # Reset value of the register. This an accumulation 
                                          # of the all reset values of the sub-fields 
    rv32:                                 # this node and its subsequent fields can exist 
                                          # if [M/S/U]XL value can be 1
      accessible: <boolean>               # indicates if the csr is accessible in rv32 mode or not. 
                                          # When False, all fields below will be trimmed off 
                                          # in the checked yaml. False also indicates that 
                                          # access-exception should be generated
      fields: []                          # This should be empty always.
      shadow: <csr-name>::<register>      # which this register shadows,'none' indicates that 
                                          # this register does not shadow anything.
      shadow_type: <text>                 # indicates the type of shadowing used. Can be one of - 
                                          # rw or ro
      msb: <int>                          # msb index of the csr. max: 31, min:0
      lsb: <int>                          # lsb index of the csr. max: 31, min:0
      type:                               # type of field. Can be only one of the following
        wlrl: [list of value-descriptors] # field is wlrl and the set of legal values.
        ro_constant: <hex>                # field is readonly and will return the same value.
        ro_variable: True                 # field is readonly but the value returned depends 
                                          # on other arch-states
        warl:                             # field is warl type. Refer to WARL section
          dependency_fields: [list]    
          legal: [list of warl-string]
          wr_illegal: [list of warl-string]           
    rv64:                                 # this node and its subsequent fields can exist 
                                          # if [M/S/U]XL value can be 2
      accessible: <boolean>               # indicates if this register exists in rv64 mode 
                                          # or not. Same definition as for rv32 node.
    rv128:                                # this node and its subsequent fields can exist if 
                                          # [M/S/U]XL value can be 3
      accessible: <boolean>              # indicates if this register exists in rv128 mode 

See register `mscratch` for an example.

Indexed CSRs
------------

.. code-block:: yaml

  <name>:                                 # name of the csr
    description: <text>                   # textual description of the csr
    address: <hex>                        # address of the csr
    priv_mode: <D/M/H/S/U>                # privilege mode that owns the register
    indexing_reg: <true/false>            # indicates that this register is an indexed type CSR
    rv32:                                 # this node and its subsequent fields can exist 
                                          # if [M/S/U]XL value can be 1
      accessible: <boolean>               # indicates if the csr is accessible in rv32 mode or not. 
                                          # When False, all fields below will be trimmed off 
                                          # in the checked yaml. False also indicates that 
                                          # access-exception should be generated
      msb: <int>                          # msb index of the csr. max: 31, min:0
      lsb: <int>                          # lsb index of the csr. max: 31, min:0
      index_select_reg: <text>            # this field should contain the name the CSR that is used
                                          # as an index select register
      index_list: <dictionary>            # this field is a list of dictionaries.
        - index_val:                      # value of the index select register that will select
                                          # this particular element
          reset-val:                      # reset value of this element in the list
          shadow: <csr-name>::<register>  # which this register shadows,'none' indicates that 
                                          # this register does not shadow anything.
          shadow_type: <text>             # indicates the type of shadowing used. Can be one of - 
                                          # rw or ro
          type:                               # type of field. Can be only one of the following
            wlrl: [list of value-descriptors] # field is wlrl and the set of legal values.
            ro_constant: <hex>                # field is readonly and will return the same value.
            ro_variable: True                 # field is readonly but the value returned depends 
                                              # on other arch-states
            warl:                             # field is warl type. Refer to WARL section
              dependency_fields: [list]    
              legal: [list of warl-string]
              wr_illegal: [list of warl-string]           
    rv64:                                 # this node and its subsequent fields can exist 
                                          # if [M/S/U]XL value can be 2
      accessible: <boolean>               # indicates if this register exists in rv64 mode 
                                          # or not. Same definition as for rv32 node.
    rv128:                                # this node and its subsequent fields can exist if 
                                          # [M/S/U]XL value can be 3
      accessible: <boolean>              # indicates if this register exists in rv128 mode 

See register `tdata` in debug yaml for an example.


Constraints
-----------

Each csr undergoes the following checks:

  1. All implemented fields at the csr-level, if set to True, are checked if
     they comply with the supported_xlen field of the ISA yaml.
  2. The reset-val is checked against compliance with the type field specified
     by the user. All unimplemented fields are considered to be hardwired to 0.

For each of the above templates the following fields for all standard csrs
defined by the spec are frozen and **CANNOT** be modified by the user.

  * description
  * address
  * priv_mode
  * fields
  * shadow
  * msb
  * lsb
  * The type field for certain csrs (like readonly) is also constrained.
  * fields names also cannot be modified for standard csrs

Only the following fields can be modified by the user:

* reset-value
* type
* implemented

Example
-------

Following is an example of how a user can define the mtvec csr in the input ISA YAML for a 
32-bit core:

.. code-block:: yaml

  mtvec:
  reset-val: 0x80010000
  rv32:
    accessible: true
    base:
      implemented: true
      type:                             
        warl: 
          dependency_fields: [mtvec::mode]
          legal:
            - "mode[1:0] in [0] -> base[29:0] in [0x20000000, 0x20004000]"             # can take only 2 fixed values in direct mode.
            - "mode[1:0] in [1] -> base[29:6] in [0x000000:0xF00000] base[5:0] in [0x00]" # 256 byte aligned values only in vectored mode.
          wr_illegal:
            - "mode[1:0] in [0] -> Unchanged"
            - "mode[1:0] in [1] && writeval in [0x2000000:0x4000000] -> 0x2000000"
            - "mode[1:0] in [1] && writeval in [0x4000001:0x3FFFFFFF] -> Unchanged"
    mode:
      implemented: true
      type:                             
        warl:
          dependency_fields: []
          legal: 
            - "mode[1:0] in [0x0:0x1] # Range of 0 to 1 (inclusive)"
          wr_illegal:
            - "Unchanged"

The following is what the riscv-config will output after performing relevant checks on the 
above user-input:

.. code-block:: yaml

    mtvec:
      description: MXLEN-bit read/write register that holds trap vector configuration.
      address: 773
      priv_mode: M
      reset-val: 0x80010000
      rv32:
        accessible: true
        base:
          implemented: true
          type:
            warl:
              dependency_fields: [mtvec::mode, writeval]
              legal:
              - 'mode[1:0] in [0] -> base[29:0] in [0x20000000, 0x20004000]'               # can take only 2 fixed values in direct mode.
              - 'mode[1:0] in [1] -> base[29:6] in [0x000000:0xF00000] base[5:0] in [0x00]'   # 256 byte aligned values only in vectored mode.
              wr_illegal:
              - 'mode[1:0] in [0] -> Unchanged'
              - 'mode[1:0] in [1] && writeval in [0x2000000:0x4000000] -> 0x2000000'
              - 'mode[1:0] in [1] && writeval in [0x4000001:0x3FFFFFFF] -> Unchanged'
          description: Vector base address.
          shadow: none
          msb: 31
          lsb: 2
        mode:
          implemented: true
          type:
            warl:
              dependency_fields: []
              legal:
              - 'mode[1:0] in [0x0:0x1] # Range of 0 to 1 (inclusive)'
              wr_illegal:
              - Unchanged
    
          description: Vector mode.
          shadow: none
          msb: 1
          lsb: 0
        fields:
        - mode
        - base 
      rv64:
        accessible: false

WARL field Definition
=====================

Since the RISC-V privilege spec indicates several csrs and sub-fields of csrs to be WARL (Write-Any-Read-Legal), 
it is necessary to provide a common scheme of representation which can precisely 
define the functionality of any such WARL field/register.


Value Descriptors
-----------------

Value descriptors are standard syntaxes that are used to define values in any
part of the WARL string. The 2 basic descriptors are : distinct-values and
range-values as described below:

  * **distinct-values** - This specifies that only the particular value should be added to the set.
      
    .. code-block:: python
        
      val
      
  * **range** - This specifies that all the values greater than or equal to lower and less than or equal to upper is to be included in the set.
         
    .. code-block:: python
         
      lower:upper

For any variable in the WARL string, the values can an amalgamation of
distinct-values and/or range-values. They are typically captured in a list as
shown in the below examples:

    
Example:
     
.. code-block:: python

  # To represent the set {0, 1, 2, 3, 4, 5}
    [0:5]

  # To represent the set {5, 10, 31}
    [5, 10, 31]

  # To represent the set {2, 3, 4, 5, 10, 11, 12, 13, 50}
    [2:5, 10:13, 50]
      
WARL Node definition
--------------------

A typical WARL node (used for a WARL csr or subfield) has the following skeleton 
in the riscv-config:

.. code-block:: yaml

   warl:   
      dependency_fields: [list of csrs/subfields that legal values depend on]
      legal: [list of strings adhering to the warl-syntax for legal assignments]
      wr_illegal: [list of strings ahdering to the warl-syntax for illegal assignments]

- **dependency_fields** : This is a list of csrs/subfields whose values affect
  the legal values of the csr under question. ``::`` is used as a hierarchy
  separator to indicate subfields. This list can be empty to indicate that the
  csr under question is not affected by any other architectural state. The
  ordering of the csr/subfields has no consequence. Examples of the list are 
  provided below:

  ..  code-block:: yaml

      - dependency_fields: [mtvec::mode]
      - dependency_fields: [misa::mxl, mepc]
  
  The following keywords are reserved and can be used accordingly in the
  dependency_fields list: 

    - ``writeval`` : to represent dependency on the current value being written 
      to the csr/subfield
    - ``currval`` : to represent dependency on the value of the csr/subfield
      before performing the write operation

  **Restrictions imposed**: The following restrictions are imposed on the
  elements of the list:

    1. The csrs/subfields mentioned in the list must have their 
       accessible/implemented fields set to True in the isa yaml.

  **Micro-Architectural Dependencies**
  
  riscv-config supports the notion of listing micro-architectural dependencies
  in the dependency_fields list.

  **Listing uArch Dependencies**

  All uArch dependencies need to be listed in the custom specification. An example
  node has been described as follows:

  .. code-block:: yaml

    uarch_signals:
      uarch_signal_1:
        msb: integer
        lsb: integer
        reset-val: integer
        legal: list
      uarch_signal_2:
        msb: integer
        lsb: integer
        reset-val: integer
        legal: list
      uarch_group_1:
        subfields:
          uarch_signal_3:
            msb: integer
            lsb: integer
            reset-val: integer
            legal: list
          uarch_signal_4:
            msb: integer
            lsb: integer
            reset-val: integer
            legal: list

  .. note:: The custom csr specification is now validated using a custom_schema.yaml

  **Restrictions imposed**:
  
  1. uArch depedencies can be listed in either of the two ways,
    as a uArch group or as an independent list of uArch signals. While using a uArch
    group, the name of the group must have a ``uarch_`` prefix. The following is
    an example of a uArch group listed in the dependencies:

    .. code-block:: yaml

      warl:
        dependency_fields: [uarch_cachecontrol::global_valid, uarch_cachecontrol::global_dirty]
        legal:
          - global_valid[3:0] in [0] and global_dirty[3:0] in [0]
            -> base[61:0] bitmask [0x3FFFFFFFFFFFFFFF, 0x0000000000000000]
        wr_illegal:
          - Unchanged

    **NOTE**: The above example shows a dependency string only consisting of uArch
    signals grouped under the name ``uarch_cachecontrol``. We can also include other
    spec based dependencies in the same list.

  2. While listing the uArch dependencies as an independent list, the name of the
    uArch signals must not have a ``uarch_`` prefix. The following is an example
    of a uArch dependency listed as an independent list:

    .. code-block:: yaml

      warl:
        dependency_fields: [uarch_global_valid, uarch_global_dirty, mstatus::mpp]
        legal:
          - uarch_global_valid[3:0] in [0] and uarch_global_dirty[3:0] in [0]
            -> base[61:0] bitmask [0x3FFFFFFFFFFFFFFF, 0x0000000000000000]
        wr_illegal:
          - Unchanged

    **NOTE**: In the above example, the uArch signals are listed as independent
    signals, not grouped under any name. The riscv-config tool will automatically
    group them under the name ``uarch_signals`` (internally) for ease of
    parsing the rest of the YAML. These signals would be expected to reside as
    independent uArch signals in the custom specification.

  **Parsing uArch dependencies**

    riscv-config internally creates a ``uarch_depends`` dictionary in a ``warl_class``
    object. This dictionary is used to store the uArch dependencies. It performs
    a lookup on the ``uarch_signals`` node from the custom spec for all checks.
    None of these dependencies are removed while generating the checked output YAML.

- **legal** : This field is a list of strings which define the warl functions of
  the csr/subfield. Each string needs to adhere to the following warl-syntax:

  .. code-block::

     dependency_string -> legal_value_string

  The ``dependency_string`` substring is basically a string defining a boolean 
  condition based on the dependent csrs (those listed in the
  ``dependency_fields``). Only when the boolean condition is satisfied, the
  corresponding warl function defined in ``legal_value_string`` substring is
  evaluated. A write only occurs when the evaluation of the
  ``legal_value_string`` also is True. The symbol ``->`` is used to denote 
  `implies` and is primarily used to split the string in to the above two 
  substrings. If none of the entries in the list evaluate to True, then the
  current write value is considered illegal and the actions defined by the
  `wr_illegal` field is carried out.

  The substrings ``dependency_string ->`` is optional. If the ``dependency_fields`` list is
  empty, then the substring ``dependency_string ->`` must be omitted from the warl string.

  The ``dependency_string`` and the ``legal_value_string`` both follow the same
  legal syntax:

  .. code-block::

     <variable-name>[<hi-index>:<lo-index>] <op> <value-descriptors>

  The ``variable-name`` field can be the name a csr or a subfield (without the
  hierarchical delimiter ``::``). Within the ``dependency_string`` substring the variable
  names can only be those listed in the ``dependency_fields`` list. In the
  ``legal_value_string`` substring however, the ``variable-name`` should be
  either `writeval` or the name the csr or the subfield (without the
  hierarchical delimiter ``::``) that the warl node belongs to.

  The indices fields ``hi-index`` and ``lo-index`` are used to indicate the bit
  range of the variable that being looked-up or modified. The basic constraints
  are that ``hi-index`` must be greater than the ``lo-index``. If only a
  single-bit is being looked-up/assigned, then ``:lo-index`` can be skipped.
  This definition applies to both the ``dependency_string`` and the
  ``legal_value_string``.

  The ``op`` field in the ``dependency_string`` substring can be one of ``in``
  or ``not in`` to indicate that the variable takes the values defined in the
  ``value-descriptors`` field or does not take those values respectively. In
  addition to the above operators, the ``legal_value_string`` can include one
  more operator : ``bitmask``. When using the ``bitmask`` operator the
  value-descriptors have to be a list of two distinct-values as follows:

  .. code-block:: yaml

     csr_name[hi:lo] bitmask [mask, fixedval]

  Both the ``mask`` and ``fixedval`` fields are integers. All bits set in the
  mask indicates writable bits of the variable. All bits bits cleared in the
  mask indicate bits with a constant value which is derived from the
  corresponding bit in the fixedval field.

  Since the ``dependency_string`` is supposed to represent a boolean condition,
  it also has the flexibility to use basic boolean operators like ``&&`` and
  ``||`` around the above legal syntax. Examples are provided below:

  .. code-block:: yaml

     (csrA[2:0] in [0, 1]) && (csrB[5:0] in [0:25] || csrB[5:0] in [31,30]) ->

    
  **Restrictions imposed**: The following restrictions are imposed on the above
  substrings:
  
    1. No element of the value-descriptors must exceed the maximum value which 
       can be supported by the indices of the csr/subfield. 
    2. The csrs/subfields used in the ``dependency_string`` must be in those
       listed in the ``dependency_fields`` list.
    3. Valid operators in the ``dependency_string`` substring are ``in`` and ``not in``.
    4. Valid operators in the ``legal_value_string`` substring are ``in``, ``not in`` and ``bitmask``
    5. Within the ``legal_value_string`` substrings the legal values of all bits 
       of the csr/subfield must be specified. No bits must be left undefined.
    6. If the ``dependency_fields`` is empty, then only one legal string must be
       defined in this list. 
    7. The first combination of the ``dependency_string`` and ``legal_value_string`` 
       to evaluate to True, starting from the top of the list is given highest
       priority to define the next legal value of the csr/subfield.
    8. The reset-value of the csr/subfield must cause atleast one of the legal
       strings in the list to evaluate to True.

  **Assumptions**

    1. Since the list of all ``dependency_string`` substrings is not required to 
       be exhaustively defined
       by the user, if none of the ``dependency_strings`` in the list evaluate to
       true, then the current write operation should be treated as an illegal
       write operation, and the action defined by the ``wr_illegal`` node must be
       carried out.
    2. If one of the dependent csrs/subfield defined in the
       ``dependency_fields`` is not used in the ``dependency_strings``, then it
       implictly assumed that, the variable does not affect the legal value for
       that string

- **wr_illegal** : This field takes in a list of strings which define the next 
  legal value of the field when an illegal value is being written to the 
  csr/subfield. Each string needs to adhere to the following syntax:

  .. code-block:: yaml

      dependency_string -> update_mode

  The ``dependency_string`` follows the same rules, assumptions and restrictions
  described above. When the ``dependency_string`` evaluates to True the
  ``update_mode`` substring defines the next legal value of the csr/subfield.
  The supported values of the ``update_mode`` string are :

      - **Unchanged**: The value remains unchanged to the current legal value held in the csr/subfield.
      - **<val>**: A single value can also be specified
      - **Nextup**: ceiling(*writeval*) i.e. the next larger or the largest element of the legal list
      - **Nextdown**: floor(*writeval*) i.e. the next smallest or the smallest element of the legal list
      - **Nearup**: celing(*writeval*) i.e. the closest element in the list, with the larger element being chosen in case of a tie.
      - **Neardown**: floor(*writeval*) i.e. the closes element in the list, with the smaller element being chosen in case of a tie
      - **Max**: maximum of all legal values
      - **Min**: minimum of all legal values
      - **Addr**: 

        .. code-block:: python

          if ( val < base || val > bound)
              return Flip-MSB of field

Examples
--------
  
.. code-block:: yaml

    # When base of mtvec depends on the mode field.
    WARL: 
      dependency_fields: [mtvec::mode]
      legal:
        - "mode[1:0] in [0] -> base[29:0] in [0x20000000, 0x20004000]"  # can take only 2 fixed values when mode==0.
        - "mode[1:0] in [1] -> base[29:6] in [0x000000:0xF00000] base[5:0] in [0x00]" # 256 byte aligned when mode==1
      wr_illegal:
        - "mode[1:0] in [0] -> unchanged"
        - "mode[1:0] in [1] && writeval in [0x2000000:0x4000000] -> 0x2000000" # predefined value if write value is
        - "mode[1:0] in [1] && writeval in [0x4000001:0x3FFFFFFF] -> unchanged"

    # When base of mtvec depends on the mode field. Using bitmask instead of range
    WARL: 
      dependency_fields: [mtvec::mode]
      legal:
        - "mode[1:0] in [0] -> base[29:0] in [0x20000000, 0x20004000]"  # can take only 2 fixed values when mode==0.
        - "mode[1:0] in [1] -> base[29:0] bitmask [0x3FFFFFC0, 0x00000000]" # 256 byte aligned when mode==1
      wr_illegal:
        - "mode[1:0] in [0] -> unchanged" # no illegal for bitmask defined legal strings.
        - Unchanged
        

    # no dependencies. Mode field of mtvec can take only 2 legal values using range-descriptor
    WARL:
      dependency_fields:
      legal: 
        - "mode[1:0] in [0x0:0x1] # Range of 0 to 1 (inclusive)"
      wr_illegal:
        - "0x00"

    # no dependencies. using single-value-descriptors
    WARL:
      dependency_fields:
      legal: 
        - "mode[1:0] in [0x0,0x1] # Range of 0 to 1 (inclusive)"
      wr_illegal:
        - "0x00"

.. _platform_yaml_spec:

Platform YAML Spec
==================

This section describes each node of the PLATFORM-YAML. For each node, we have identified the fields required from the user and also the various constraints involved.

.. include:: schema_platform.rst

Debug YAML Spec
===============

.. include:: schema_debug.rst

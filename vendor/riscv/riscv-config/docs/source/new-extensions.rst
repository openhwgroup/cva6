#################################
Adding support for new Extensions
#################################

Adding support for a new ISA extension or an adjoining spec to RISCV-CONFIG could entail one or more of the following updates:

1. Updating the ISA string and its constraints to recognize valid configurations of the new
   extension
2. Updating the schema_isa.yaml with new CSRs defined by the new ISA extension
3. Adding new schemas and a new cli argument for supporting adjoining RISC-V specs like debug, trace, etc.

This chapter will descrive how one can go about RISC-V achieving the above tasks.

Updates to the ISA string
=========================

Modifications in constants.py
----------------------------------------

As shown in the example below, any new extensions and sub extensions have to be enabled by adding them in 
the regex expression of the `isa_regex <https://github.com/riscv/riscv-config/blob/master/riscv_config/constants.py>`_ node. Following is an instance of the node
for reference:

.. code-block:: python

  Z_extensions = [
          "Zicbom", "Zicbop", "Zicboz", "Zicsr", "Zifencei", "Zihintpause",
          "Zam",
          "Zfh",
          "Zfinx", "Zdinx", "Zhinx", "Zhinxmin",
          "Ztso",
          "Zba", "Zbb", "Zbc", "Zbe", "Zbf", "Zbkb", "Zbkc", "Zbkx", "Zbm", "Zbp", "Zbr", "Zbs", "Zbt",
          "Zk", "Zkn", "Zknd", "Zkne", "Zknh", "Zkr", "Zks", "Zksed", "Zksh", "Zkt",
          "Zmmul",
          "Svnapot"
  ]
  isa_regex = \
          re.compile("^RV(32|64|128)[IE][ACDFGHJLMNPQSTUVX]*(("+'|'.join(Z_extensions)+")(_("+'|'.join(Z_extensions)+"))*){,1}$")

.. note:: If you are adding a new Z extension, note that it must be added to the list (Z_extensions) above the regex.
   This list will be used to generate the correct matching regex, with two instances of each Z extension; first one
   immediately after the standard extension in the format `|Zgargle`. This is to support
   that fact that the new Z extension could start immediately after the standard extensions which an
   underscore. The second will be after the first set of Z extensions in the format `(_(...|Zgargle)`.


Adding constraints in the isa_validator.py file
---------------------------------------------------------

While adding a new extension to the ISA string, there can be certain legal and illegal combinations which cannot be
easily expressed using the regex above. These checks need to be added to the function
`get_extension_list <https://github.com/riscv-software-src/riscv-config/blob/master/riscv_config/isa_validator.py#L4>`_ 
present in the `isa_validatory.py` file.

The above function returns a tuple of 3 elements:

 1. ``extension_list``: A list of all valid extensions that can be extracted from the ISA string.
 2. ``err``: a boolean value indicating if an error exists in the ISA string
 3. ``err_list``: A list of all errors encountered during the parsing of the string.

The function behaves as follows:
 
  1. The input ISA string is matched against the above regex. A mismatch will cause a return from the
     function with ``err`` set to True and ``extension_list`` containing the required message 
     (`here <https://github.com/riscv-software-src/riscv-config/blob/master/riscv_config/isa_validator.py#L8-L11>`_).
  2. Next we split the string into a list where each element is a valid extension (standard,
     Z-extension or S-extension) present in the ISA string. The ordering of the extensions in the
     list corresponds to their ordering present in the ISA string (`here <https://github.com/riscv-software-src/riscv-config/blob/master/riscv_config/isa_validator.py#L14-L28>`_).
  3. We then check for valid canonical ordering of extensions in the ISA string. If any issues are
     found, then ``err`` is set to True and ``err_list`` is updated with a corresponding error message.
     (`here <https://github.com/riscv-software-src/riscv-config/blob/master/riscv_config/isa_validator.py#L29-L38>`_)

  4. Similar canonical ordering checks for performed for the Z extension subsets as well 
     (`here <https://github.com/riscv-software-src/riscv-config/blob/master/riscv_config/isa_validator.py#L40-L51>`_).
  5. Finally, a series of `if` based checks are performed on the ``extension_list`` to see if any
     illegal combination exists (`here <https://github.com/riscv-software-src/riscv-config/blob/master/riscv_config/isa_validator.py#L53-L58>`_)

For a majority of new extension additions - only point 5 above needs attention. 

Following is an example of the constraints imposed by the Crypto-Scalar extesions which require
additional checks according to point-5 above. The sub-extensions Zkn and Zks are supersets of a 
combination of other Zk* abbreviations. Thus, if the superset extension exists in the ISA, 
none of the corresponding subset ZK* should be present in the ISA at the same time.


**Constraints used here** : 

   1.If Zkn is present , its subset extensions Zkne, Zknh, Zknd, Zbkc and Zbkb cannot be present in the ISA string.  

   2.If Zks is present , its subset extensions Zksed, Zksh, Zbkx, Zbkc and Zbkb cannot be present in the ISA string.

The pythone snippet to capture the above is presented below:

.. code-block:: python

  (...)
  if 'Zkn' in extension_list and ( set(['Zbkb', 'Zbkc', 'Zbkx', 'Zkne', 'Zknd', 'Zknh']) & set(extension_list)):
    err_list.append( "Zkn is a superset of Zbkb, Zbkc, Zbkx, Zkne, Zknd, Zknh. In presence of Zkn the subsets must be ignored in the ISA string.")
    err = True
  if 'Zks' in extension_list and ( set(['Zbkb', 'Zbkc', 'Zbkx', 'Zksed', 'Zksh']) & set(extension_list) ):
    err_list.append( "Zks is a superset of Zbkb, Zbkc, Zbkx, Zksed, Zksh. In presence of Zks the subsets must be ignored in the ISA string.")
    err = True

At the end, the function returns the tuple ``(extension_list, err, err_list)``. One should consider
treating the contents of the ``extension_list`` as valid, only when ``err`` is set to False.

Assing new CSR definitions
===========================

There are two parts to addition of a new csr definition to riscv-config

Addition of new csrs to schema
------------------------------

The first step is to add the schema of the new csr in the `schema_isa.yaml
<https://github.com/riscv/riscv-config/blob/master/riscv_config/schemas/schema_isa.yaml>`_ file.
Following is an example of how the `stval` csr of the "S" extension is a added to the schema.

For each csr the author is free to define and re-use existing ``check_with`` functions to impose
further legal conditions. These ``check_with`` functions are defined in the file:
`schemaValidator.py <https://github.com/riscv/riscv-config/blob/master/riscv_config/schemaValidator.py>`_.

.. note:: in the schemaValidator the function name must be prefixed with ``_check_with`` followed by
   the name of the function defined in the ``check_with`` field of the csr.


.. code-block:: yaml

   stval:
      type: dict
      schema:
        description:
          type: string
          default: The stval is a warl register that holds the address of the instruction
            which caused the exception.
        address: {type: integer, default: 0x143, allowed: [0x143]}
        priv_mode: {type: string, default: S, allowed: [S]}
        reset-val:
          type: integer
          default: 0
          check_with: max_length
        rv32:
          type: dict
          check_with: s_check
          schema:
            fields: {type: list, default: []}
            shadow: {type: string, default: , nullable: True}
            msb: {type: integer, default: 31, allowed: [31]}
            lsb: {type: integer, default: 0, allowed: [0]}
            type:
              type: dict
              schema: { warl: *ref_warl }
              default:
                warl:
                  dependency_fields: []
                  legal:
                  - stval[31:0] in [0x00000000:0xFFFFFFFF]
                  wr_illegal:
                  - unchanged
    
            accessible:
              type: boolean
              default: true
              check_with: rv32_check
          default: {accessible: false}
        rv64:
          type: dict
          check_with: s_check
          schema:
            fields: {type: list, default: []}
            shadow: {type: string, default: , nullable: True}
            msb: {type: integer, default: 63, allowed: [63]}
            lsb: {type: integer, default: 0, allowed: [0]}
            type:
              type: dict
              schema: { warl: *ref_warl }
              default:
                warl:
                  dependency_fields: []
                  legal:
                  - stval[63:0] in [0x00000000:0xFFFFFFFFFFFFFFFF]
                  wr_illegal:
                  - unchanged
    
            accessible:
              default: true
              check_with: rv64_check
          default: {accessible: false}

The check_with function used in stval above would be defined as follows : 

.. code-block:: python

    def _check_with_rv32_check(self, field, value):
      global xlen
      if value:
          if not rv32:
              self._error( field, "Register cannot be implemented in rv32 mode due to unsupported xlen.")

    def _check_with_rv64_check(self, field, value):
      global xlen
      if value:
          if not rv64:
              self._error( field, "Register cannot be implemented in rv64 mode due to unsupported xlen.")

    def _check_with_max_length(self, field, value):
      '''Function to check whether the given value is less than the maximum value that can be stored(2^xlen-1).'''
      global supported_xlen
      global extensions
      maxv = max(supported_xlen)
      if value > (2**maxv) - 1:
          self._error(field, "Value exceeds max supported length")

    def _check_with_s_check(self, field, value):
        s = 18
        check = False
        if 'implemented' in value:
            if value['implemented']:
                check = True
        if 'accessible' in value:
            if value['accessible']:
                check = True

        if rv64 and check:
            mxl = format(extensions, '#066b')
            if (mxl[65 - s:66 - s] != '1'):
                self._error(field, "should not be implemented since S is not present")

        elif rv32 and check:
            mxl = format(extensions, '#034b')
            if (mxl[33 - s:34 - s] != '1'):
                self._error(field, "should not be implemented S is not present")


          
          
Adding default setters in checker.py
------------------------------------

The next step in adding a new csr definition is to add its default values. This is done in
`checker.py <https://github.com/riscv/riscv-config/blob/master/riscv_config/checker.py>`_

Example of adding a default setter for `stval` is show below. This code basically makes the stval
csr accessible by default when the "S" extension is enabled in the ISA string.

.. code-block:: python
   
   schema_yaml['stval']['default_setter'] = sregsetter
   
.. code-block:: python
  
   def sregset():
    '''Function to set defaults based on presence of 'S' extension.'''
    global inp_yaml
    temp = {'rv32': {'accessible': False}, 'rv64': {'accessible': False}}
    if 'S' in inp_yaml['ISA']:
      if 32 in inp_yaml['supported_xlen']:
        temp['rv32']['accessible'] = True
      if 64 in inp_yaml['supported_xlen']:
        temp['rv64']['accessible'] = True
    return temp

          

Adding support for Adjoining RISC-V specs
=========================================

Adding new CLI
--------------

For supporting any new adjoining specs, they need to be supplied via a new cli (command line
interface) argument. This new argument needs to be added in the to the parser module in 
`Utils.py <https://github.com/riscv/riscv-config/tree/master/riscv_config/utils.py#L106>`_.

The code below shows an example of how the debug spec is added as an argument to the cli parser
module:

.. code-block:: python

   parser.add_argument('--debug_spec', '-dspec', type=str, metavar='YAML', default=None, help='The YAML which contains the debug csr specs.') 


Adding a new schema
-------------------

Each new adjoining spec must have a YAML schema defined in the `schemas
<https://github.com/riscv/riscv-config/tree/master/riscv_config/schemas>`_ directory.


Adding checks through checker.py and SchemaValidator.py
-------------------------------------------------------

The user might want to add more custom checks in checker.py and SchemaValidator.py for the adjoining
spec.

For example the check_debug_specs() is a function that ensures the isa and debug specifications 
conform to their schemas. For details on check_debug_specs() check here : :ref:`checker`.

Details on the checks like s_debug_check() and u_debug_check, that can also be added to 
SchemaValidator.py are here: :ref:`schemaValidator`.

Modifications in Constants.py
-----------------------------

The new schema must be added in the constants.py to detect its path globally across other files.

.. code-block:: python

     debug_schema = os.path.join(root, 'schemas/schema_debug.yaml')
     
Performing new spec checks
--------------------------

Finally, in the main.py file the user must call the relevant functions from checker.py for
validating the inputs against the schema.


.. code-block:: python

        if args.debug_spec is not None:
            if args.isa_spec is None:
             logger.error(' Isa spec missing, Compulsory for debug')
            checker.check_debug_specs(os.path.abspath(args.debug_spec), isa_file, work_dir, True, args.no_anchors)
           



# Accellera Universal Verification Methodology (UVM, IEEE 1800.2-2017)

# Scope

This kit provides a Systemverilog library matching the requirements of [IEEE 1800.2-2017](https://ieeexplore.ieee.org/document/7932212/). 
See details in the Library Release Description below.

# Kit version

1800.2-2017 0.9

This kit was generated based upon the following git commit state: 2a9099a 3b09d5c884d821157817ba7b6487f955b34d59ad.

# License

The UVM kit is licensed under the Apache-2.0 license.  The full text of
the Apache license is provided in this kit in the file [LICENSE.txt](./LICENSE.txt).

# Copyright

All copyright owners for this kit are listed in [NOTICE.txt](./NOTICE.txt).

All Rights Reserved Worldwide


# Installing the kit

Installation of UVM requires first unpacking the kit in a convenient
location.

```
    % mkdir path/to/convenient/location
    % cd path/to/convenient/location
    % gunzip -c path/to/UVM/distribution/tar.gz | tar xvf -
```

Follow the installation instructions provided by your tool vendor for
using this UVM installation and tool version dependencies.

# Prerequisites

- IEEE1800 compliant SV simulator. Please check with your tool vendor for exact tool version requirements.
- C compiler to compile the DPI code (if not otherwise provided by tool vendor)


# Library Release description

Each class and method in the standard is annotated in the implementation, allowing tools to identify 
the corresponding section in the standard. 

Example:
```
// @uvm-ieee 1800.2-2017 auto 16.5.3.2
extern virtual function void get_packed_bits (ref bit unsigned stream[]);
```
In addition to the APIs described in the standard, the Library includes the following categories of extra API:

1. API used within the library, not intended to be public. 
2. Debug aids
3. Deprecated UVM 1.2 API\
**Note:** The deprecated UVM 1.2 APIs are under a `` `ifdef UVM_ENABLE_DEPRECATED_API `` guard.  These APIs are
only supported when the UVM 1.2 API didn't contradict 1800.2-2017 API.  When `UVM_ENABLE_DEPRECATED_API` is defined
both the 1.2 and 1800.2 APIs are available.  When `UVM_ENABLE_DEPRECATED_API` is _not_ defined, the UVM 1.2
APIs are not available, and any code referencing them will miscompile.\
\
By default, `UVM_ENABLE_DEPRECATED_API` is not  defined. 
4. Additional API / Enhancements

**Note:** As the documentation for this release is incomplete, it may not be obvious which category any given non-1800.2 API
falls into.  As such, APIs missing the `// @uvm-ieee ...` tag should be used with caution.  If you have any questions regarding 
an untagged API, please direct them to the Accellera UVM Working Group (uvm-wg@lists.accellera.org).

# Deviations from the standard and the provided implementation

There are instances where this library has deviated from the 1800.2 standard. These are:

1. [Mantis 6417](https://accellera.mantishub.io/view.php?id=6417) Additional API Methods for random seeding based on the full name rather than object creation order were omitted from the standard. (See Section F.4.3/4):

```
  virtual function bit uvm_coreservice_t::get_uvm_seeding(); 
  virtual function void uvm_coreservice_t::set_uvm_seeding (bit enable);
```

2. [Mantis 6377](https://accellera.mantishub.io/view.php?id=6377) The standard provides for a way to get all the callbacks attached to an object.  The implementation adds an additional argument to the method to overcome the issue of resolving  the instance specific callbacks. 

The implemented signature is:
<pre>
  static function void get_all ( ref CB all_callbacks[$] <b>, input T obj=null</b> ); 
</pre>

3. [Mantis 6423](https://accellera.mantishub.io/view.php?id=6423) The standard Sections 16.5.3.1 and 16.5.3.2 indicate the set_packed_* methods as being signed while the uvm_object::unpack methods are specified as unsigned. The implemented methods are:

<pre>
virtual function void uvm_packer::set_packed_bits( ref bit <b>unsigned</b> stream[] );
virtual function void uvm_packer::set_packed_bytes( ref byte <b>unsigned</b> stream[] );
virtual function void uvm_packer::set_packed_ints( ref int <b>unsigned</b> stream[] );
virtual function void uvm_packer::set_packed_longints( ref longint <b>unsigned</b> stream[] );

virtual function void uvm_packer::get_packed_bits( ref bit <b>unsigned</b> stream[] );
virtual function void uvm_packer::get_packed_bytes( ref byte <b>unsigned</b> stream[] );
virtual function void uvm_packer::get_packed_ints( ref int <b>unsigned</b> stream[] );
virtual function void uvm_packer::get_packed_longints( ref longint <b>unsigned</b> stream[] );
</pre>

4. [Mantis 6260](https://accellera.mantishub.io/view.php?id=6260) uvm_phase::get_objection is made a virtual function to ensure uniformity with the raise_objection() and drop_objection() methods.  The standard does not define this method as virtual, and users could theoretically get different results if the method was non-virtual.

<pre>
  <b>virtual</b> function int uvm_phase::get_objection_count( uvm_object obj=null );
</pre>

5. [Mantis 6482](https://accellera.mantishub.io/view.php?id=6482) The printer and comparer have methods for configuration, each of which is effectively cleared via a call to `flush()`.  Since `uvm_object` calls flush on these policies, it effectively wipes out any user defined values.  The implementation does _NOT_ clear these values on a flush.

6. [Mantis 6308](https://accellera.mantishub.io/view.php?id=6308) The library implements the get_default() method in the uvm_printer extensions with an exception that an instance of the relevant printer is created if the previous corresponding call to set_default() for that extension was null. 

7. [Mantis 6591](https://accellera.mantishub.io/view.php?id=6591) The library implements `uvm_recorder::do_record_object` as virtual even though the standard calls for pure virtual.

<pre>
  <del>pure</del> virtual protected function void do_record_object(string name, uvm_object value);
</pre>

8. [Mantis 5940](https://accellera.mantishub.io/view.php?id=5940) uvm_resource_db::read_by_type and uvm_resource_db::read_by_name deviate from the standard as they defines the <val> argument as inout, whereas the standard defines it as an output.

<pre>
  static function bit uvm_resource_db::read_by_type(input string scope, <b>inout</b> T val, input uvm_object accessor = null);
  static function bit uvm_resource_db::read_by_name(input string scope, input string name, <b>inout</b> T val, input uvm_object accessor = null);
</pre>

# Backwards Compatibility Concerns

These are instances wherein the functionality of an API that exists in both UVM 1.2 and the IEEE 1800.2 standard has changed in a non 
backwards-compatible manner.

1. [Mantis 6644](https://accellera.mantishub.io/view.php?id=6644) Changes to big endian support in uvm_reg_map.  In previous versions of UVM, configuring a uvm_reg_map to UVM_BIG_ENDIAN didn't change the byte ordering for data (effectively always forcing LITTLE endian, regardless of configuration).  This has been corrected in the 1800.2 release, such that the data provided to the adapter is now properly ordered.  Users can update their adapter to handle the new properly ordered data, or configure their map to UVM_LITTLE_ENDIAN.
                             
# Migration instructions

In order to migrate to the Library version of the release, It is recommended that you perform the following steps to get your code to 
run with this release of UVM. 

1. Compile/Run using a UVM1.2 library with `UVM_NO_DEPRECATED` defined. This will ensure that your code runs 
with UVM 1.2 which was a baseline for the IEEE 1800.2 standard development.  

**Note:** All code deprecated in UVM 1.2 has been removed from this version of the library.

2. Compile/Run using this library with `UVM_ENABLE_DEPRECATED_API` defined.  This step helps identify the areas where your code may need modifications to comply with the standard.


3. Compile/Run using this library without `UVM_ENABLE_DEPRECATED_API` defined. Removing the define ensures that only the 1800.2 API documented in the standard, along with any non-deprecation accellera supplied API, is used.  Any new compile failures are the result of deprecated 1.2 APIs.

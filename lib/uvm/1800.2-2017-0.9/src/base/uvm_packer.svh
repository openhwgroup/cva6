//
//------------------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2014 Intel Corporation
// Copyright 2018 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2017 Cisco Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
// CLASS -- NODOCS -- uvm_packer
//
// The uvm_packer class provides a policy object for packing and unpacking
// uvm_objects. The policies determine how packing and unpacking should be done.
// Packing an object causes the object to be placed into a bit (byte or int)
// array. If the `uvm_field_* macro are used to implement pack and unpack,
// by default no metadata information is stored for the packing of dynamic
// objects (strings, arrays, class objects).
//
//-------------------------------------------------------------------------------

typedef bit signed [(`UVM_PACKER_MAX_BYTES*8)-1:0] uvm_pack_bitstream_t;

// @uvm-ieee 1800.2-2017 auto 16.5.1
class uvm_packer extends uvm_policy;

   // @uvm-ieee 1800.2-2017 auto 16.5.2.3
   `uvm_object_utils(uvm_packer)

  // Function: set_packed_*
  // Implementation of P1800.2 16.5.3.1
  //
  // The LRM specifies the set_packed_* methods as being
  // signed, whereas the <uvm_object::unpack> methods are specified
  // as unsigned.  This is being tracked in Mantis 6423.
  //
  // The reference implementation has implemented these methods
  // as unsigned so as to remain consistent.
  //
  //| virtual function void set_packed_bits( ref bit unsigned stream[] );
  //| virtual function void set_packed_bytes( ref byte unsigned stream[] );
  //| virtual function void set_packed_ints( ref int unsigned stream[] );
  //| virtual function void set_packed_longints( ref longint unsigned stream[] );
   
  // @uvm-ieee 1800.2-2017 auto 16.5.3.1
  extern virtual function void set_packed_bits (ref bit unsigned stream[]);

  // @uvm-ieee 1800.2-2017 auto 16.5.3.1
  extern virtual function void set_packed_bytes (ref byte unsigned stream[]);

  // @uvm-ieee 1800.2-2017 auto 16.5.3.1
  extern virtual function void set_packed_ints (ref int unsigned stream[]);

  // @uvm-ieee 1800.2-2017 auto 16.5.3.1
  extern virtual function void set_packed_longints (ref longint unsigned stream[]);
   
  // Function: get_packed_*
  // Implementation of P1800.2 16.5.3.2
  //
  // The LRM specifies the get_packed_* methods as being
  // signed, whereas the <uvm_object::pack> methods are specified
  // as unsigned.  This is being tracked in Mantis 6423.
  //
  // The reference implementation has implemented these methods
  // as unsigned so as to remain consistent.
  //
  //| virtual function void get_packed_bits( ref bit unsigned stream[] );
  //| virtual function void get_packed_bytes( ref byte unsigned stream[] );
  //| virtual function void get_packed_ints( ref int unsigned stream[] );
  //| virtual function void get_packed_longints( ref longint unsigned stream[] );
   
  // @uvm-ieee 1800.2-2017 auto 16.5.3.2
  extern virtual function void get_packed_bits (ref bit unsigned stream[]);

  // @uvm-ieee 1800.2-2017 auto 16.5.3.2
  extern virtual function void get_packed_bytes (ref byte unsigned stream[]);

  // @uvm-ieee 1800.2-2017 auto 16.5.3.2
  extern virtual function void get_packed_ints (ref int unsigned stream[]);

  // @uvm-ieee 1800.2-2017 auto 16.5.3.2
  extern virtual function void get_packed_longints (ref longint unsigned stream[]);
   
  //----------------//
  // Group -- NODOCS -- Packing //
  //----------------//

  // @uvm-ieee 1800.2-2017 auto 16.5.2.4
  static function void set_default (uvm_packer packer) ;
     uvm_coreservice_t coreservice ;
     coreservice = uvm_coreservice_t::get() ;
     coreservice.set_default_packer(packer) ;
  endfunction

  // @uvm-ieee 1800.2-2017 auto 16.5.2.5
  static function uvm_packer get_default () ;
     uvm_coreservice_t coreservice ;
     coreservice = uvm_coreservice_t::get() ;
     return coreservice.get_default_packer() ;
  endfunction

  
  // @uvm-ieee 1800.2-2017 auto 16.5.2.2
  extern virtual function void flush ();
  // Function -- NODOCS -- pack_field
  //
  // Packs an integral value (less than or equal to 4096 bits) into the
  // packed array. ~size~ is the number of bits of ~value~ to pack.

  // @uvm-ieee 1800.2-2017 auto 16.5.4.8
  extern virtual function void pack_field (uvm_bitstream_t value, int size);


  // Function -- NODOCS -- pack_field_int
  //
  // Packs the integral value (less than or equal to 64 bits) into the
  // pack array.  The ~size~ is the number of bits to pack, usually obtained by
  // ~$bits~. This optimized version of <pack_field> is useful for sizes up
  // to 64 bits.

  // @uvm-ieee 1800.2-2017 auto 16.5.2.1
  extern function new(string name="");

  // @uvm-ieee 1800.2-2017 auto 16.5.4.9
  extern virtual function void pack_field_int (uvm_integral_t value, int size);


  // @uvm-ieee 1800.2-2017 auto 16.5.4.1
  extern virtual function void pack_bits(ref bit value[], input int size = -1);


  // @uvm-ieee 1800.2-2017 auto 16.5.4.10
  extern virtual function void pack_bytes(ref byte value[], input int size = -1);


  // @uvm-ieee 1800.2-2017 auto 16.5.4.11
  extern virtual function void pack_ints(ref int value[], input int size = -1);

  // recursion functions


   
  // Function -- NODOCS -- pack_string
  //
  // Packs a string value into the pack array. 
  //
  // When the metadata flag is set, the packed string is terminated by a ~null~
  // character to mark the end of the string.
  //
  // This is useful for mixed language communication where unpacking may occur
  // outside of SystemVerilog UVM.

  // @uvm-ieee 1800.2-2017 auto 16.5.4.5
  extern virtual function void pack_string (string value);


  // Function -- NODOCS -- pack_time
  //
  // Packs a time ~value~ as 64 bits into the pack array.

  // @uvm-ieee 1800.2-2017 auto 16.5.4.6
  extern virtual function void pack_time (time value); 


  // Function -- NODOCS -- pack_real
  //
  // Packs a real ~value~ as 64 bits into the pack array. 
  //
  // The real ~value~ is converted to a 6-bit scalar value using the function
  // $real2bits before it is packed into the array.

  // @uvm-ieee 1800.2-2017 auto 16.5.4.7
  extern virtual function void pack_real (real value);


  // Function -- NODOCS -- pack_object
  //
  // Packs an object value into the pack array. 
  //
  // A 4-bit header is inserted ahead of the string to indicate the number of
  // bits that was packed. If a ~null~ object was packed, then this header will
  // be 0. 
  //
  // This is useful for mixed-language communication where unpacking may occur
  // outside of SystemVerilog UVM.

  // @uvm-ieee 1800.2-2017 auto 16.5.4.2
  extern virtual function void pack_object (uvm_object value);


  //------------------//
  // Group -- NODOCS -- Unpacking //
  //------------------//
  
  // Function -- NODOCS -- is_null
  //
  // This method is used during unpack operations to peek at the next 4-bit
  // chunk of the pack data and determine if it is 0.
  //
  // If the next four bits are all 0, then the return value is a 1; otherwise
  // it is 0. 
  //
  // This is useful when unpacking objects, to decide whether a new object
  // needs to be allocated or not.

  // @uvm-ieee 1800.2-2017 auto 16.5.4.3
  extern virtual function bit is_null ();


  // Function -- NODOCS -- unpack_field
  //
  // Unpacks bits from the pack array and returns the bit-stream that was
  // unpacked. ~size~ is the number of bits to unpack; the maximum is 4096 bits.

  // @uvm-ieee 1800.2-2017 auto 16.5.4.16
  extern virtual function uvm_bitstream_t unpack_field (int size);

  // Function -- NODOCS -- unpack_field_int
  //
  // Unpacks bits from the pack array and returns the bit-stream that was
  // unpacked. 
  //
  // ~size~ is the number of bits to unpack; the maximum is 64 bits. 
  // This is a more efficient variant than unpack_field when unpacking into
  // smaller vectors.

  // @uvm-ieee 1800.2-2017 auto 16.5.4.17
  extern virtual function uvm_integral_t unpack_field_int (int size);


  // @uvm-ieee 1800.2-2017 auto 16.5.4.18
  extern virtual function void unpack_bits(ref bit value[], input int size = -1);


  // @uvm-ieee 1800.2-2017 auto 16.5.4.19
  extern virtual function void unpack_bytes(ref byte value[], input int size = -1);


  // @uvm-ieee 1800.2-2017 auto 16.5.4.12
  extern virtual function void unpack_ints(ref int value[], input int size = -1);
   

  // Function -- NODOCS -- unpack_string
  //
  // Unpacks a string. 
  //
  // num_chars bytes are unpacked into a string. If num_chars is -1 then
  // unpacking stops on at the first ~null~ character that is encountered.

  // @uvm-ieee 1800.2-2017 auto 16.5.4.13
  extern virtual function string unpack_string ();


  // Function -- NODOCS -- unpack_time
  //
  // Unpacks the next 64 bits of the pack array and places them into a
  // time variable.

  // @uvm-ieee 1800.2-2017 auto 16.5.4.14
  extern virtual function time unpack_time (); 


  // Function -- NODOCS -- unpack_real
  //
  // Unpacks the next 64 bits of the pack array and places them into a
  // real variable. 
  //
  // The 64 bits of packed data are converted to a real using the $bits2real
  // system function.

  // @uvm-ieee 1800.2-2017 auto 16.5.4.15
  extern virtual function real unpack_real ();


  // Function -- NODOCS -- unpack_object
  //
  // Unpacks an object and stores the result into ~value~. 
  //
  // ~value~ must be an allocated object that has enough space for the data
  // being unpacked. The first four bits of packed data are used to determine
  // if a ~null~ object was packed into the array.
  //
  // The <is_null> function can be used to peek at the next four bits in
  // the pack array before calling this method.

  // @uvm-ieee 1800.2-2017 auto 16.5.4.4
  extern virtual function void unpack_object (uvm_object value);


  // Function -- NODOCS -- get_packed_size
  //
  // Returns the number of bits that were packed.

  // @uvm-ieee 1800.2-2017 auto 16.5.3.3
  extern virtual function int get_packed_size(); 


  //------------------//
  // Group -- NODOCS -- Variables //
  //------------------//

`ifdef UVM_ENABLE_DEPRECATED_API
  // Variable -- NODOCS -- physical
  //
  // This bit provides a filtering mechanism for fields.
  //
  // The <abstract> and physical settings allow an object to distinguish between
  // two different classes of fields. It is up to you, in the
  // <uvm_object::do_pack> and <uvm_object::do_unpack> methods, to test the
  // setting of this field if you want to use it as a filter.

  bit physical = 1;


  // Variable -- NODOCS -- abstract
  //
  // This bit provides a filtering mechanism for fields. 
  //
  // The abstract and physical settings allow an object to distinguish between
  // two different classes of fields. It is up to you, in the
  // <uvm_object::do_pack> and <uvm_object::do_unpack> routines, to test the
  // setting of this field if you want to use it as a filter.

  bit abstract;


  // Variable -- NODOCS -- big_endian
  //
  // This bit determines the order that integral data is packed (using
  // <pack_field>, <pack_field_int>, <pack_time>, or <pack_real>) and how the
  // data is unpacked from the pack array (using <unpack_field>,
  // <unpack_field_int>, <unpack_time>, or <unpack_real>). When the bit is set,
  // data is associated msb to lsb; otherwise, it is associated lsb to msb. 
  //
  // The following code illustrates how data can be associated msb to lsb and
  // lsb to msb:
  //
  //|  class mydata extends uvm_object;
  //|
  //|    logic[15:0] value = 'h1234;
  //|
  //|    function void do_pack (uvm_packer packer);
  //|      packer.pack_field_int(value, 16);
  //|    endfunction
  //|
  //|    function void do_unpack (uvm_packer packer);
  //|      value = packer.unpack_field_int(16);
  //|    endfunction
  //|  endclass
  //|
  //|  mydata d = new;
  //|  bit bits[];
  //|
  //|  initial begin
  //|    d.pack(bits);  // 'b0001001000110100
  //|    uvm_default_packer.big_endian = 0;
  //|    d.pack(bits);  // 'b0010110001001000
  //|  end

  bit big_endian = 1;
`endif

  // variables and methods primarily for internal use

  static bit bitstream[];   // local bits for (un)pack_bytes
  static bit fabitstream[]; // field automation bits for (un)pack_bytes
  int        m_pack_iter; // Used to track the bit of the next pack
  int        m_unpack_iter; // Used to track the bit of the next unpack

  bit   reverse_order;      //flip the bit order around
  byte  byte_size     = 8;  //set up bytesize for endianess
  int   word_size     = 16; //set up worksize for endianess
  bit   nopack;             //only count packable bits

  uvm_pack_bitstream_t m_bits;

  extern virtual function void unpack_object_ext  (inout uvm_object value);

`ifdef UVM_ENABLE_DEPRECATED_API
  extern virtual function bit  unsigned get_bit  (int unsigned index);
  extern virtual function byte unsigned get_byte (int unsigned index);
  extern virtual function int  unsigned get_int  (int unsigned index);

  extern virtual function void get_bits (ref bit unsigned bits[]);
  extern virtual function void get_bytes(ref byte unsigned bytes[]);
  extern virtual function void get_ints (ref int unsigned ints[]);

  extern virtual function void put_bits (ref bit unsigned bitstream[]);
  extern virtual function void put_bytes(ref byte unsigned bytestream[]);
  extern virtual function void put_ints (ref int unsigned intstream[]);

  extern virtual function void set_packed_size(); 
`endif
   
  extern function void index_error(int index, string id, int sz);
  extern function bit enough_bits(int needed, string id);

`ifdef UVM_ENABLE_DEPRECATED_API
  extern function void reset();
`endif
  
endclass



//------------------------------------------------------------------------------
// IMPLEMENTATION
//------------------------------------------------------------------------------

// NOTE- max size limited to BITSTREAM bits parameter (default: 4096)


// index_ok
// --------

function void uvm_packer::index_error(int index, string id, int sz);
    uvm_report_error("PCKIDX", 
        $sformatf("index %0d for get_%0s too large; valid index range is 0-%0d.",
                  index,id,((m_pack_iter+sz-1)/sz)-1), UVM_NONE);
endfunction


// enough_bits
// -----------

function bit uvm_packer::enough_bits(int needed, string id);
  if ((m_pack_iter - m_unpack_iter) < needed) begin
    uvm_report_error("PCKSZ",
        $sformatf("%0d bits needed to unpack %0s, yet only %0d available.",
                  needed, id, (m_pack_iter - m_unpack_iter)), UVM_NONE);
    return 0;
  end
  return 1;
endfunction


// get_packed_size
// ---------------

function int uvm_packer::get_packed_size();
  return m_pack_iter-m_unpack_iter;
endfunction


`ifdef UVM_ENABLE_DEPRECATED_API
// set_packed_size
// ---------------

function void uvm_packer::set_packed_size();
  /* doesn't actually do anything now */
endfunction

// reset
// -----

function void uvm_packer::reset();
  flush();
endfunction

function void uvm_packer::get_bits( ref bit bits [] ); get_packed_bits(bits); endfunction
function void uvm_packer::get_bytes( ref byte unsigned bytes [] ); get_packed_bytes(bytes); endfunction
function void uvm_packer::get_ints( ref int unsigned ints [] ); get_packed_ints(ints); endfunction
`endif

function void uvm_packer::flush();
  // The iterators are spaced 64b from the beginning, enough to store
  // the iterators during get_packed_* and retrieve them during
  // set_packed_*.  Without this, set_packed_[byte|int|longint] will
  // move the iterators too far.
  m_pack_iter = 64;
  m_unpack_iter = 64;
  m_bits       = 0;
  super.flush();
endfunction : flush

// get_packed_bits
// --------

function void uvm_packer::get_packed_bits(ref bit unsigned stream[]);
  stream        = new[m_pack_iter];
  m_bits[31:0]  = m_pack_iter; /* Reserved bits */
  m_bits[63:32] = m_unpack_iter; /* Reserved bits */
  for (int i=0;i<m_pack_iter;i++)
    stream[i] = m_bits[i];
endfunction

`ifdef UVM_ENABLE_DEPRECATED_API
// When deprecated, we support big_endian
`define M__UVM_GET_PACKED(T) \
function void uvm_packer::get_packed_``T``s (ref T unsigned stream[] ); \
   int sz;                                                              \
   T v;                                                                 \
   sz = (m_pack_iter + $high(v)) / $bits(T);                            \
   stream = new[sz];                                                    \
   m_bits[31:0] = m_pack_iter; /* Reserved Bits */                      \
   m_bits[63:32] = m_unpack_iter; /* Reserved Bits */                   \
   foreach (stream[i]) begin                                            \
      if (i != sz-1 || (m_pack_iter % $bits(T)) == 0)                   \
	v = m_bits[ i* $bits(T) +: $bits(T) ];                          \
      else                                                              \
	v = m_bits[ i* $bits(T) +: $bits(T) ] & ({$bits(T){1'b1}} >> ($bits(T)-(m_pack_iter%$bits(T)))); \
      if(big_endian)                                                    \
	v = {<<{v}};                                                    \
      stream[i] = v;                                                    \
   end                                                                  \
endfunction 
`else // !`ifdef UVM_ENABLE_DEPRECATED_API
`define M__UVM_GET_PACKED(T) \
function void uvm_packer::get_packed_``T``s (ref T unsigned stream[] ); \
   int sz;                                                              \
   T v;                                                                 \
   sz = (m_pack_iter + $high(v)) / $bits(T);                            \
   m_bits[31:0] = m_pack_iter; /* Reserved Bits */                      \
   m_bits[63:32] = m_unpack_iter; /* Reserved Bits */                   \
   stream = new[sz];                                                    \
   foreach (stream[i]) begin                                            \
      if (i != sz-1 || (m_pack_iter % $bits(T)) == 0)                   \
	v = m_bits[ i* $bits(T) +: $bits(T) ];                          \
      else                                                              \
	v = m_bits[ i* $bits(T) +: $bits(T) ] & ({$bits(T){1'b1}} >> ($bits(T)-(m_pack_iter%$bits(T)))); \
      stream[i] = v;                                                    \
   end                                                                  \
endfunction 
`endif // !`ifdef UVM_ENABLE_DEPRECATED_API

`M__UVM_GET_PACKED(byte)
`M__UVM_GET_PACKED(int)
`M__UVM_GET_PACKED(longint)

`undef M__UVM_GET_PACKED

`ifdef UVM_ENABLE_DEPRECATED_API
function void uvm_packer::put_bits( ref bit bitstream [] ); set_packed_bits(bitstream); endfunction
function void uvm_packer::put_bytes( ref byte unsigned bytestream [] ); set_packed_bytes(bytestream); endfunction
function void uvm_packer::put_ints( ref int unsigned intstream [] ); set_packed_ints(intstream); endfunction
`endif

// set_packed_bits
// --------

function void uvm_packer::set_packed_bits (ref bit stream []);

  int bit_size;

  bit_size = stream.size();

`ifdef UVM_ENABLE_DEPRECATED_API
  if(big_endian)
    for (int i=bit_size-1;i>=0;i--)
      m_bits[i] = stream[i];
  else
`endif
    for (int i=0;i<bit_size;i++)
      m_bits[i] = stream[i];

  m_pack_iter = m_bits[31:0]; /* Reserved Bits */
  m_unpack_iter = m_bits[63:32]; /* Reserved Bits */
 
endfunction

`ifdef UVM_ENABLE_DEPRECATED_API
// In deprecated mode we support big_endian
`define M__UVM_SET_PACKED(T) \
function void uvm_packer::set_packed_``T``s (ref T unsigned stream []); \
   int count;                                                           \
   foreach(stream[i]) begin                                             \
     if (big_endian)                                                    \
       m_bits[count +: $bits(T)] = {<<{stream[i]}};                     \
     else                                                               \
       m_bits[count +: $bits(T)] = stream[i];                           \
     count += $bits(T);                                                 \
   end                                                                  \
  m_pack_iter = m_bits[31:0]; /* Reserved Bits */                       \
  m_unpack_iter = m_bits[63:32]; /* Reserved Bits */                    \
endfunction 
`else // !`ifdef UVM_ENABLE_DEPRECATED_API
`define M__UVM_SET_PACKED(T) \
function void uvm_packer::set_packed_``T``s (ref T unsigned stream []); \
   int count;                                                           \
   foreach(stream[i]) begin                                             \
     m_bits[count +: $bits(T)] = stream[i];                             \
     count += $bits(T);                                                 \
   end                                                                  \
  m_pack_iter = m_bits[31:0]; /* Reserved Bits */                       \
  m_unpack_iter = m_bits[63:32]; /* Reserved Bits */                    \
endfunction 
`endif

`M__UVM_SET_PACKED(byte)
`M__UVM_SET_PACKED(int)
`M__UVM_SET_PACKED(longint)

`undef M__UVM_SET_PACKED

`ifdef UVM_ENABLE_DEPRECATED_API
// get_bit
// -------

function bit unsigned uvm_packer::get_bit(int unsigned index);
  if (index >= m_pack_iter)
    index_error(index, "bit",1);
  return m_bits[index];
endfunction


// get_byte
// --------

function byte unsigned uvm_packer::get_byte(int unsigned index);
  if (index >= (m_pack_iter+7)/8)
    index_error(index, "byte",8);
  return m_bits[index*8 +: 8];
endfunction


// get_int
// -------

function int unsigned uvm_packer::get_int(int unsigned index);
  if (index >= (m_pack_iter+31)/32)
    index_error(index, "int",32);
  return m_bits[(index*32) +: 32];
endfunction
`endif

// PACK


// pack_object
// ---------

function void uvm_packer::pack_object(uvm_object value);
  uvm_field_op field_op;
  if (value == null ) begin
    m_bits[m_pack_iter +: 4] = 0;
    m_pack_iter += 4;
    return ;
  end
  else begin
    m_bits[m_pack_iter +: 4]  = 4'hF;
    m_pack_iter += 4;
  end
  
  push_active_object(value);
  field_op = uvm_field_op::m_get_available_op() ;
  field_op.set(UVM_PACK,this,value);
  value.do_execute_op(field_op);
  if (field_op.user_hook_enabled()) begin
    value.do_pack(this);
  end
  field_op.m_recycle();
  void'(pop_active_object());
endfunction

  
// pack_real
// ---------

function void uvm_packer::pack_real(real value);
  pack_field_int($realtobits(value), 64);
endfunction
  

// pack_time
// ---------

function void uvm_packer::pack_time(time value);
  pack_field_int(value, 64);
  //m_bits[m_pack_iter +: 64] = value; this overwrites endian adjustments
endfunction
  

// pack_field
// ----------

function void uvm_packer::pack_field(uvm_bitstream_t value, int size);
  for (int i=0; i<size; i++)
`ifdef UVM_ENABLE_DEPRECATED_API
    if(big_endian == 1)
      m_bits[m_pack_iter+i] = value[size-1-i];
    else
`endif
      m_bits[m_pack_iter+i] = value[i];
  m_pack_iter += size;
endfunction
  

// pack_field_int
// --------------

function void uvm_packer::pack_field_int(uvm_integral_t value, int size);
  for (int i=0; i<size; i++)
`ifdef UVM_ENABLE_DEPRECATED_API
    if(big_endian == 1)
      m_bits[m_pack_iter+i] = value[size-1-i];
    else
`endif
      m_bits[m_pack_iter+i] = value[i];
  m_pack_iter += size;
endfunction
  
// pack_bits
// -----------------

function void uvm_packer::pack_bits(ref bit value[], input int size = -1);
   if (size < 0)
     size = value.size();

   if (size > value.size()) begin
      `uvm_error("UVM/BASE/PACKER/BAD_SIZE",
                 $sformatf("pack_bits called with size '%0d', which exceeds value.size() of '%0d'",
                           size,
                           value.size()))
      return;
   end
   
   for (int i=0; i<size; i++)
`ifdef UVM_ENABLE_DEPRECATED_API
     if (big_endian == 1)
       m_bits[m_pack_iter+i] = value[size-1-i];
     else
`endif
       m_bits[m_pack_iter+i] = value[i];
   m_pack_iter += size;
endfunction 

// pack_bytes
// -----------------

function void uvm_packer::pack_bytes(ref byte value[], input int size = -1);
   int max_size = value.size() * $bits(byte);
   
   if (size < 0)
     size = max_size;

   if (size > max_size) begin
      `uvm_error("UVM/BASE/PACKER/BAD_SIZE",
                 $sformatf("pack_bytes called with size '%0d', which exceeds value size of '%0d'",
                           size,
                           max_size))
      return;
   end
   else begin
      int idx_select;

      for (int i=0; i<size; i++) begin
`ifdef UVM_ENABLE_DEPRECATED_API
         if (big_endian == 1)
           idx_select = size-1-i;
         else
`endif
           idx_select = i;
         
         m_bits[m_pack_iter+i] = value[idx_select / $bits(byte)][idx_select % $bits(byte)];
      end
   
      m_pack_iter += size;
   end
endfunction 

// pack_ints
// -----------------

function void uvm_packer::pack_ints(ref int value[], input int size = -1);
   int max_size = value.size() * $bits(int);
   
   if (size < 0)
     size = max_size;

   if (size > max_size) begin
      `uvm_error("UVM/BASE/PACKER/BAD_SIZE",
                 $sformatf("pack_ints called with size '%0d', which exceeds value size of '%0d'",
                           size,
                           max_size))
      return;
   end
   else begin
      int idx_select;

      for (int i=0; i<size; i++) begin
`ifdef UVM_ENABLE_DEPRECATED_API
         if (big_endian == 1)
           idx_select = size-1-i;
         else
`endif
           idx_select = i;
         
         m_bits[m_pack_iter+i] = value[idx_select / $bits(int)][idx_select % $bits(int)];
      end
   
      m_pack_iter += size;
   end
endfunction 


// pack_string
// -----------

function void uvm_packer::pack_string(string value);
  byte b;
`ifdef UVM_ENABLE_DEPRECATED_API
  foreach (value[index]) begin
    if(big_endian == 1) begin
      b = value[index];
      for(int i=0; i<8; ++i)
        m_bits[m_pack_iter+i] = b[7-i];
    end 
    else 
      m_bits[m_pack_iter +: 8] = value[index];
    m_pack_iter += 8;
  end
`else // !`ifdef UVM_ENABLE_DEPRECATED_API
  foreach (value[index]) begin
     m_bits[m_pack_iter +: 8] = value[index];
     m_pack_iter += 8;
  end
`endif // !`ifdef UVM_ENABLE_DEPRECATED_API
   m_bits[m_pack_iter +: 8] = 0;
   m_pack_iter += 8;
endfunction 


// UNPACK


// is_null
// -------

function bit uvm_packer::is_null();
    return (m_bits[m_unpack_iter+:4]==0);
endfunction

// unpack_object
// -------------

function void uvm_packer::unpack_object_ext(inout uvm_object value);
  unpack_object(value);
endfunction

function void uvm_packer::unpack_object(uvm_object value);
  uvm_field_op field_op;
  
  if (is_null()) begin
    if (value != null) begin
      `uvm_error("UVM/BASE/PACKER/UNPACK/N2NN", "attempt to unpack a null object into a not-null object!")
      return;
    end
    m_unpack_iter += 4; // advance past the null
    return;
  end
  else begin
    if (value == null) begin
      `uvm_error("UVM/BASE/PACKER/UNPACK/NN2N", "attempt to unpack a non-null object into a null object!")
      return;
    end
    m_unpack_iter += 4; // advance past the !null
    push_active_object(value);
    field_op = uvm_field_op::m_get_available_op() ;
    field_op.set(UVM_UNPACK,this,value);
    value.do_execute_op(field_op);
    if (field_op.user_hook_enabled()) begin
       value.do_unpack(this);
    end
    field_op.m_recycle();
    void'(pop_active_object());
  end

endfunction

  
// unpack_real
// -----------

function real uvm_packer::unpack_real();
  if (enough_bits(64,"real")) begin
    return $bitstoreal(unpack_field_int(64));
  end
endfunction
  

// unpack_time
// -----------

function time uvm_packer::unpack_time();
  if (enough_bits(64,"time")) begin
    return unpack_field_int(64);
  end
endfunction
  

// unpack_field
// ------------

function uvm_bitstream_t uvm_packer::unpack_field(int size);
  unpack_field = 'b0;
  if (enough_bits(size,"integral")) begin
    m_unpack_iter += size;
    for (int i=0; i<size; i++)
`ifdef UVM_ENABLE_DEPRECATED_API
      if(big_endian == 1)
        unpack_field[i] = m_bits[m_unpack_iter-i-1];
      else
`endif
        unpack_field[i] = m_bits[m_unpack_iter-size+i];
  end
endfunction
  

// unpack_field_int
// ----------------

function uvm_integral_t uvm_packer::unpack_field_int(int size);
  unpack_field_int = 'b0;
  if (enough_bits(size,"integral")) begin
    m_unpack_iter += size;
    for (int i=0; i<size; i++)
`ifdef UVM_ENABLE_DEPRECATED_API
      if(big_endian == 1)
        unpack_field_int[i] = m_bits[m_unpack_iter-i-1];
      else
`endif
        unpack_field_int[i] = m_bits[m_unpack_iter-size+i];
  end
endfunction
  
// unpack_bits
// -------------------

function void uvm_packer::unpack_bits(ref bit value[], input int size = -1);
   if (size < 0)
     size = value.size();

   if (size > value.size()) begin
      `uvm_error("UVM/BASE/PACKER/BAD_SIZE",
                 $sformatf("unpack_bits called with size '%0d', which exceeds value.size() of '%0d'",
                           size,
                           value.size()))
      return;
   end
   
   if (enough_bits(size, "integral")) begin
      m_unpack_iter += size;
      for (int i=0; i<size; i++)
`ifdef UVM_ENABLE_DEPRECATED_API
        if (big_endian == 1)
          value[i] = m_bits[m_unpack_iter-i-1];
        else
`endif
          value[i] = m_bits[m_unpack_iter-size+i];
   end
endfunction

// unpack_bytes
// -------------------

function void uvm_packer::unpack_bytes(ref byte value[], input int size = -1);
   int max_size = value.size() * $bits(byte);
   if (size < 0)
     size = max_size;

   if (size > max_size) begin
      `uvm_error("UVM/BASE/PACKER/BAD_SIZE",
                 $sformatf("unpack_bytes called with size '%0d', which exceeds value size of '%0d'",
                           size,
                           value.size()))
      return;
   end
   else begin
      if (enough_bits(size, "integral")) begin
         m_unpack_iter += size;

         for (int i=0; i<size; i++) begin
`ifdef UVM_ENABLE_DEPRECATED_API
            if (big_endian == 1)
              value[ i / $bits(byte) ][ i % $bits(byte) ] = m_bits[m_unpack_iter-i-1];
            else
`endif
              value[ i / $bits(byte) ][ i % $bits(byte) ] = m_bits[m_unpack_iter-size+i];
         
         end
      end // if (enough_bits(size, "integral"))
   end
endfunction

// unpack_ints
// -------------------

function void uvm_packer::unpack_ints(ref int value[], input int size = -1);
   int max_size = value.size() * $bits(int);
   if (size < 0)
     size = max_size;

   if (size > max_size) begin
      `uvm_error("UVM/BASE/PACKER/BAD_SIZE",
                 $sformatf("unpack_ints called with size '%0d', which exceeds value size of '%0d'",
                           size,
                           value.size()))
      return;
   end
   else begin
      if (enough_bits(size, "integral")) begin
         m_unpack_iter += size;

         for (int i=0; i<size; i++) begin
`ifdef UVM_ENABLE_DEPRECATED_API
            if (big_endian == 1)
              value[ i / $bits(int) ][ i % $bits(int) ] = m_bits[m_unpack_iter-i-1];
            else
`endif
              value[ i / $bits(int) ][ i % $bits(int) ] = m_bits[m_unpack_iter-size+i];
         end   
      end
   end
endfunction


// unpack_string
// -------------

// If num_chars is not -1, then the user only wants to unpack a
// specific number of bytes into the string.
function string uvm_packer::unpack_string();
  byte b;
  int i; i=0;

  while(enough_bits(8,"string") && 
        (m_bits[m_unpack_iter+:8] != 0) )
  begin
    // silly, because cannot append byte/char to string
    unpack_string = {unpack_string," "};
`ifdef UVM_ENABLE_DEPRECATED_API
    if(big_endian == 1) begin
      for(int j=0; j<8; ++j)
        b[7-j] = m_bits[m_unpack_iter+j];
      unpack_string[i] = b;
    end 
    else
`endif
      unpack_string[i] = m_bits[m_unpack_iter +: 8];
    m_unpack_iter += 8;
    ++i;
  end
  if(enough_bits(8,"string"))
    m_unpack_iter += 8;
endfunction 


// Constructor implementation
function uvm_packer::new(string name="");
  super.new(name);
  flush();
endfunction



//
//------------------------------------------------------------------------------
// Copyright 2007-2011 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2017 Intel Corporation
// Copyright 2010-2014 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2013 Verilab
// Copyright 2012 AMD
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2014-2018 Cisco Systems, Inc.
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

// File -- NODOCS -- Miscellaneous Structures

//------------------------------------------------------------------------------
//
// Class -- NODOCS -- uvm_void
//
// The ~uvm_void~ class is the base class for all UVM classes. It is an abstract
// class with no data members or functions. It allows for generic containers of
// objects to be created, similar to a void pointer in the C programming
// language. User classes derived directly from ~uvm_void~ inherit none of the
// UVM functionality, but such classes may be placed in ~uvm_void~-typed
// containers along with other UVM objects.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 5.2
virtual class uvm_void;
endclass

// Append/prepend symbolic values for order-dependent APIs
typedef enum {UVM_APPEND, UVM_PREPEND} uvm_apprepend;

// Forward declaration since scope stack uses uvm_objects now
typedef class uvm_object;

typedef class uvm_coreservice_t;
typedef class uvm_factory;

typedef class uvm_config_db;
// m_uvm_config_obj_misc is an internal typedef for the uvm_misc.svh file
// to use. UVM users should use the uvm_config_object typedef
typedef uvm_config_db#(uvm_object) m_uvm_config_obj_misc;


typedef class uvm_comparer ;
typedef class uvm_packer ;
typedef class uvm_recorder ;
typedef class uvm_printer ;

// Variable- uvm_global_random_seed
//
// Create a seed which is based off of the global seed which can be used to seed
// srandom processes but will change if the command line seed setting is 
// changed.
//
int unsigned uvm_global_random_seed = $urandom;


// Class- uvm_seed_map
//
// This map is a seed map that can be used to update seeds. The update
// is done automatically by the seed hashing routine. The seed_table_lookup
// uses an instance name lookup and the seed_table inside a given map
// uses a type name for the lookup.
//
class uvm_seed_map;
  int unsigned seed_table [string];
  int unsigned count [string];
endclass

uvm_seed_map uvm_random_seed_table_lookup [string];


//------------------------------------------------------------------------------
// Internal utility functions
//------------------------------------------------------------------------------

// Function- uvm_instance_scope
//
// A function that returns the scope that the UVM library lives in, either
// an instance, a module, or a package.
//
function string uvm_instance_scope();
  byte c;
  int pos;
  //first time through the scope is ~null~ and we need to calculate, afterwards it
  //is correctly set.

  if(uvm_instance_scope != "") 
    return uvm_instance_scope;

  $swrite(uvm_instance_scope, "%m");
  //remove the extraneous .uvm_instance_scope piece or ::uvm_instance_scope
  pos = uvm_instance_scope.len()-1;
  c = uvm_instance_scope[pos];
  while(pos && (c != ".") && (c != ":")) 
    c = uvm_instance_scope[--pos];
  if(pos == 0)
    uvm_report_error("SCPSTR", $sformatf("Illegal name %s in scope string",uvm_instance_scope));
  uvm_instance_scope = uvm_instance_scope.substr(0,pos);
endfunction


// Function- uvm_oneway_hash
//
// A one-way hash function that is useful for creating srandom seeds. An
// unsigned int value is generated from the string input. An initial seed can
// be used to seed the hash, if not supplied the uvm_global_random_seed 
// value is used. Uses a CRC like functionality to minimize collisions.
//
parameter UVM_STR_CRC_POLYNOMIAL = 32'h04c11db6;
function int unsigned uvm_oneway_hash ( string string_in, int unsigned seed=0 );
  bit          msb;
  bit [7:0]    current_byte;
  bit [31:0]   crc1;
      
  if(!seed) seed = uvm_global_random_seed;
  uvm_oneway_hash = seed;

  crc1 = 32'hffffffff;
  for (int _byte=0; _byte < string_in.len(); _byte++) begin
     current_byte = string_in[_byte];
     if (current_byte == 0) break;
     for (int _bit=0; _bit < 8; _bit++) begin
        msb = crc1[31];
        crc1 <<= 1;
        if (msb ^ current_byte[_bit]) begin
           crc1 ^=  UVM_STR_CRC_POLYNOMIAL;
           crc1[0] = 1;
        end
     end
  end
  uvm_oneway_hash += ~{crc1[7:0], crc1[15:8], crc1[23:16], crc1[31:24]};

endfunction


// Function- uvm_create_random_seed
//
// Creates a random seed and updates the seed map so that if the same string
// is used again, a new value will be generated. The inst_id is used to hash
// by instance name and get a map of type name hashes which the type_id uses
// for its lookup.

function int unsigned uvm_create_random_seed ( string type_id, string inst_id="" );
  uvm_seed_map seed_map;

  if(inst_id == "")
    inst_id = "__global__";

  if(!uvm_random_seed_table_lookup.exists(inst_id))
    uvm_random_seed_table_lookup[inst_id] = new;
  seed_map = uvm_random_seed_table_lookup[inst_id];

  type_id = {uvm_instance_scope(),type_id};

  if(!seed_map.seed_table.exists(type_id)) begin
    seed_map.seed_table[type_id] = uvm_oneway_hash ({type_id,"::",inst_id}, uvm_global_random_seed);
  end
  if (!seed_map.count.exists(type_id)) begin
    seed_map.count[type_id] = 0;
  end

  //can't just increment, otherwise too much chance for collision, so 
  //randomize the seed using the last seed as the seed value. Check if
  //the seed has been used before and if so increment it.
  seed_map.seed_table[type_id] = seed_map.seed_table[type_id]+seed_map.count[type_id]; 
  seed_map.count[type_id]++;

  return seed_map.seed_table[type_id];
endfunction


// Function- uvm_object_value_str 
//
//
function string uvm_object_value_str(uvm_object v);
  if (v == null)
    return "<null>";
  uvm_object_value_str.itoa(v.get_inst_id());
  uvm_object_value_str = {"@",uvm_object_value_str};
endfunction


// Function- uvm_leaf_scope
//
//
function string uvm_leaf_scope (string full_name, byte scope_separator = ".");
  byte bracket_match;
  int  pos;
  int  bmatches;

  bmatches = 0;
  case(scope_separator)
    "[": bracket_match = "]";
    "(": bracket_match = ")";
    "<": bracket_match = ">";
    "{": bracket_match = "}";
    default: bracket_match = "";
  endcase

  //Only use bracket matching if the input string has the end match
  if(bracket_match != "" && bracket_match != full_name[full_name.len()-1])
    bracket_match = "";

  for(pos=full_name.len()-1; pos>0; --pos) begin
    if(full_name[pos] == bracket_match) bmatches++;
    else if(full_name[pos] == scope_separator) begin
      bmatches--;
      if(!bmatches || (bracket_match == "")) break;
    end
  end
  if(pos) begin
    if(scope_separator != ".") pos--;
    uvm_leaf_scope = full_name.substr(pos+1,full_name.len()-1);
  end
  else begin
    uvm_leaf_scope = full_name;
  end
endfunction


// Function- uvm_bitstream_to_string
//
//
function string uvm_bitstream_to_string (uvm_bitstream_t value, int size,
                                         uvm_radix_enum radix=UVM_NORADIX,
                                         string radix_str="");
  // sign extend & don't show radix for negative values
  if (radix == UVM_DEC && value[size-1] === 1)
    return $sformatf("%0d", value);

  // TODO $countbits(value,'z) would be even better
  if($isunknown(value)) begin
	  uvm_bitstream_t _t;
	  _t=0;
	  for(int idx=0;idx<size;idx++)
	    _t[idx]=value[idx];
	  value=_t;
  	end
  else 
  	value &= (1 << size)-1;

  case(radix)
    UVM_BIN:      return $sformatf("%0s%0b", radix_str, value);
    UVM_OCT:      return $sformatf("%0s%0o", radix_str, value);
    UVM_UNSIGNED: return $sformatf("%0s%0d", radix_str, value);
    UVM_STRING:   return $sformatf("%0s%0s", radix_str, value);
    UVM_TIME:     return $sformatf("%0s%0t", radix_str, value);
    UVM_DEC:      return $sformatf("%0s%0d", radix_str, value);
    default:      return $sformatf("%0s%0x", radix_str, value);
  endcase
endfunction

// Function- uvm_integral_to_string
//
//
function string uvm_integral_to_string (uvm_integral_t value, int size,
                                         uvm_radix_enum radix=UVM_NORADIX,
                                         string radix_str="");
  // sign extend & don't show radix for negative values
  if (radix == UVM_DEC && value[size-1] === 1)
    return $sformatf("%0d", value);

  // TODO $countbits(value,'z) would be even better
  if($isunknown(value)) begin
	  uvm_integral_t _t;
	  _t=0;
	  for(int idx=0;idx<size;idx++)
	  	_t[idx]=value[idx];
	  value=_t;
  	end
  else 
  	value &= (1 << size)-1;

  case(radix)
    UVM_BIN:      return $sformatf("%0s%0b", radix_str, value);
    UVM_OCT:      return $sformatf("%0s%0o", radix_str, value);
    UVM_UNSIGNED: return $sformatf("%0s%0d", radix_str, value);
    UVM_STRING:   return $sformatf("%0s%0s", radix_str, value);
    UVM_TIME:     return $sformatf("%0s%0t", radix_str, value);
    UVM_DEC:      return $sformatf("%0s%0d", radix_str, value);
    default:      return $sformatf("%0s%0x", radix_str, value);
  endcase
endfunction

// Backwards compat
function string uvm_vector_to_string(uvm_bitstream_t value, int size,
                                     uvm_radix_enum radix=UVM_NORADIX,
                                     string radix_str="");
   return uvm_bitstream_to_string(value,size,radix,radix_str);
endfunction // uvm_vector_to_string
   
// Function- uvm_get_array_index_int
//
// The following functions check to see if a string is representing an array
// index, and if so, what the index is.

function int uvm_get_array_index_int(string arg, output bit is_wildcard);
  int i;
  uvm_get_array_index_int = 0;
  is_wildcard = 1;
  i = arg.len() - 1;
  if(arg[i] == "]")
    while(i > 0 && (arg[i] != "[")) begin
      --i;
      if((arg[i] == "*") || (arg[i] == "?")) i=0;
      else if((arg[i] < "0") || (arg[i] > "9") && (arg[i] != "[")) begin
        uvm_get_array_index_int = -1; //illegal integral index
        i=0;
      end
    end
  else begin
    is_wildcard = 0;
    return 0;
  end

  if(i>0) begin
    arg = arg.substr(i+1, arg.len()-2);
    uvm_get_array_index_int = arg.atoi(); 
    is_wildcard = 0;
  end
endfunction 
  

// Function- uvm_get_array_index_string
//
//
function string uvm_get_array_index_string(string arg, output bit is_wildcard);
  int i;
  uvm_get_array_index_string = "";
  is_wildcard = 1;
  i = arg.len() - 1;
  if(arg[i] == "]")
    while(i > 0 && (arg[i] != "[")) begin
      if((arg[i] == "*") || (arg[i] == "?")) i=0;
      --i;
    end
  if(i>0) begin
    uvm_get_array_index_string = arg.substr(i+1, arg.len()-2);
    is_wildcard = 0;
  end
endfunction


// Function- uvm_is_array
//
//
function bit uvm_is_array(string arg);
  return arg[arg.len()-1] == "]";
endfunction


// Function- uvm_has_wildcard
//
//
function automatic bit uvm_has_wildcard (string arg);
  uvm_has_wildcard = 0;

  //if it is a regex then return true
  if( (arg.len() > 1) && (arg[0] == "/") && (arg[arg.len()-1] == "/") )
    return 1;

  //check if it has globs
  foreach(arg[i])
    if( (arg[i] == "*") || (arg[i] == "+") || (arg[i] == "?") )
      uvm_has_wildcard = 1;

endfunction


typedef class uvm_component;
typedef class uvm_root;
typedef class uvm_report_object;

`ifdef UVM_ENABLE_DEPRECATED_API 
//------------------------------------------------------------------------------
// CLASS -- NODOCS -- uvm_utils #(TYPE,FIELD)
//
// This class contains useful template functions.
//
//------------------------------------------------------------------------------
        
class uvm_utils #(type TYPE=int, string FIELD="config");

  typedef TYPE types_t[$];

  // Function -- NODOCS -- find_all
  //
  // Recursively finds all component instances of the parameter type ~TYPE~,
  // starting with the component given by ~start~. Uses <uvm_root::find_all>.

  static function types_t find_all(uvm_component start);
    uvm_component list[$];
    types_t types;
    uvm_root top;
    uvm_coreservice_t cs;
    cs = uvm_coreservice_t::get();
    top = cs.get_root();
    top.find_all("*",list,start);
    foreach (list[i]) begin
      TYPE typ;
      if ($cast(typ,list[i]))
        types.push_back(typ);
    end
    if (types.size() == 0) begin
      `uvm_warning("find_type-no match",{"Instance of type '",TYPE::type_name,
         " not found in component hierarchy beginning at ",start.get_full_name()})
    end
    return types;
  endfunction

  static function TYPE find(uvm_component start);
    types_t types = find_all(start);
    if (types.size() == 0)
      return null;
    if (types.size() > 1) begin
      `uvm_warning("find_type-multi match",{"More than one instance of type '",TYPE::type_name,
         " found in component hierarchy beginning at ",start.get_full_name()})
      return null;
    end
    return types[0];
  endfunction

  static function TYPE create_type_by_name(string type_name, string contxt);
    uvm_object obj;
    TYPE  typ;
    uvm_coreservice_t cs = uvm_coreservice_t::get();                                                     
    uvm_factory factory=cs.get_factory();
  
    obj = factory.create_object_by_name(type_name,contxt,type_name);
       if (!$cast(typ,obj))
         uvm_report_error("WRONG_TYPE",{"The type_name given '",type_name,
                "' with context '",contxt,"' did not produce the expected type."});
    return typ;
  endfunction


  // Function -- NODOCS -- get_config
  //
  // This method gets the object config of type ~TYPE~
  // associated with component ~comp~.
  // We check for the two kinds of error which may occur with this kind of 
  // operation.

  static function TYPE get_config(uvm_component comp, bit is_fatal);
    uvm_object obj;
    TYPE cfg;

    if (!m_uvm_config_obj_misc::get(comp,"",FIELD, obj)) begin
      if (is_fatal)
        comp.uvm_report_fatal("NO_SET_CFG", {"no set_config to field '", FIELD,
                           "' for component '",comp.get_full_name(),"'"},
                           UVM_MEDIUM, `uvm_file , `uvm_line  );
      else
        comp.uvm_report_warning("NO_SET_CFG", {"no set_config to field '", FIELD,
                           "' for component '",comp.get_full_name(),"'"},
                           UVM_MEDIUM, `uvm_file , `uvm_line  );
      return null;
    end

    if (!$cast(cfg, obj)) begin
      if (is_fatal)
        comp.uvm_report_fatal( "GET_CFG_TYPE_FAIL",
                          {"set_config_object with field name ",FIELD,
                          " is not of type '",TYPE::type_name,"'"},
                          UVM_NONE , `uvm_file , `uvm_line );
      else
        comp.uvm_report_warning( "GET_CFG_TYPE_FAIL",
                          {"set_config_object with field name ",FIELD,
                          " is not of type '",TYPE::type_name,"'"},
                          UVM_NONE , `uvm_file , `uvm_line );
    end

    return cfg;
  endfunction
endclass
`endif

`ifdef UVM_USE_PROCESS_CONTAINER
class process_container_c;
   process p;
   function new(process p_);
     p=p_;
   endfunction
endclass
`endif


// this is an internal function and provides a string join independent of a streaming pack
function automatic string m_uvm_string_queue_join(ref string i[$]);
`ifndef QUESTA
   m_uvm_string_queue_join = {>>{i}};
`else
	foreach(i[idx])
		m_uvm_string_queue_join = {m_uvm_string_queue_join,i[idx]};
`endif
endfunction


			

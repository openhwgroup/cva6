//
//------------------------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2013 Verilab
// Copyright 2014 NVIDIA Corporation
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



//----------------------------------------------------------------------
// class uvm_spell_chkr
//----------------------------------------------------------------------
class uvm_spell_chkr #(type T=int);

  typedef T tab_t[string];
  static const int unsigned max = '1;
   
  //--------------------------------------------------------------------
  // check
  //
  // primary interface to the spell checker.  The function takes two
  // arguments, a table of strings and a string to check.  The table is
  // organized as an associative array of type T.  E.g.
  //
  //    T strtab[string]
  //
  // It doesn't matter what T is since we are only concerned with the
  // string keys. However, we need T in order to make argument types
  // match.
  //
  // First, we do the simple thing and see if the string already is in
  // the string table by calling the ~exists()~ method.  If it does exist
  // then there is a match and we're done.  If the string doesn't exist
  // in the table then we invoke the spell checker algorithm to see if
  // our string is a misspelled variation on a string that does exist in
  // the table.
  //
  // The main loop traverses the string table computing the levenshtein
  // distance between each string and the string we are checking.  The
  // strings in the table with the minimum distance are considered
  // possible alternatives.  There may be more than one string in the
  // table with a minimum distance. So all the alternatives are stored
  // in a queue.
  //
  // Note: This is not a particularly efficient algorithm.  It requires
  // computing the levenshtein distance for every string in the string
  // table.  If that list were very large the run time could be long.
  // For the resources application in UVM probably the size of the
  // string table is not excessive and run times will be fast enough.
  // If, on average, that proves to be an invalid assumption then we'll
  // have to find ways to optimize this algorithm.
  //
  // note: strtab should not be modified inside check() 
  //--------------------------------------------------------------------
  static function bit check ( /* const */ ref tab_t strtab, input string s);

    string key;
    int distance;
    int unsigned min;
    string min_key[$];

    if(strtab.exists(s)) begin
      return 1;
    end

    min = max;
    foreach(strtab[key]) begin
      distance = levenshtein_distance(key, s);

      // A distance < 0 means either key, s, or both are empty.  This
      // should never happen here but we check for that condition just
      // in case.
      if(distance < 0)
        continue;

      if(distance < min) begin
        // set a new minimum.  Clean out the queue since previous
        // alternatives are now invalidated.
        min = distance;
        min_key.delete();
        min_key.push_back(key);
        continue;
      end

      if(distance == min) begin
        min_key.push_back(key);
      end

    end


    // if (min == max) then the string table is empty
    if(min == max) begin
	  `uvm_info("UVM/CONFIGDB/SPELLCHK",$sformatf("%s not located, no alternatives to suggest", s),UVM_NONE)
    end	
    else
    // dump all the alternatives with the minimum distance    
    begin
	   	string q[$];
	    
	   	foreach(min_key[i]) begin
     			q.push_back(min_key[i]);
     			q.push_back("|");
	   	end
	   	if(q.size())
	   		void'(q.pop_back());
	   		
	   	`uvm_info("UVM/CONFIGDB/SPELLCHK",$sformatf("%s not located, did you mean %s", s, `UVM_STRING_QUEUE_STREAMING_PACK(q)),UVM_NONE)
    end	
    
    return 0;

  endfunction


  //--------------------------------------------------------------------
  // levenshtein_distance
  //
  // Compute levenshtein distance between s and t
  // The Levenshtein distance is defined as The smallest number of
  // insertions, deletions, and substitutions required to change one
  // string into another.  There is a tremendous amount of information
  // available on Levenshtein distance on the internet.  Two good
  // sources are wikipedia and nist.gov.  A nice, simple explanation of
  // the algorithm is at
  // http://www.codeproject.com/KB/recipes/Levenshtein.aspx.  Use google
  // to find others.
  //
  // This implementation of the Levenshtein
  // distance computation algorithm is a SystemVerilog adaptation of the
  // C implementatiion located at http://www.merriampark.com/ldc.htm.
  //--------------------------------------------------------------------
  static local function int levenshtein_distance(string s, string t);

    int k, i, j, n, m, cost, distance;
    int d[];

    //Step 1
    n = s.len() + 1;
    m = t.len() + 1;

    if(n == 1 || m == 1)
      return -1; //a negative return value means that one or both strings are empty.

    d = new[m*n];

    //Step 2	
    for(k = 0; k < n; k++)
      d[k] = k;

    for(k = 0; k < m; k++)
      d[k*n] = k;

    //Steps 3 and 4	
    for(i = 1; i < n; i++) begin
      for(j = 1; j < m; j++) begin

        //Step 5
        cost = !(s[i-1] == t[j-1]);

        //Step 6			 
        d[j*n+i] = minimum(d[(j-1)*n+i]+1, d[j*n+i-1]+1, d[(j-1)*n+i-1]+cost);

      end
    end

    distance = d[n*m-1];
    return distance;

  endfunction

  //--------------------------------------------------------------------
  // Gets the minimum of three values
  //--------------------------------------------------------------------
  static local function int minimum(int a, int b, int c);

    int min = a;

    if(b < min)
      min = b;
    if(c < min)
      min = c;

    return min;

  endfunction

endclass

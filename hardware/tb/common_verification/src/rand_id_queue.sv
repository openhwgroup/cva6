// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Wrapper package so class can be used after `import rand_id_queue_pkg::*;`.
package rand_id_queue_pkg;

// ID Queue with Randomizing Output
class rand_id_queue #(
  type          data_t = logic,
  int unsigned  ID_WIDTH = 0
);

  localparam int unsigned N_IDS = 2**ID_WIDTH;
  localparam type id_t = logic[ID_WIDTH-1:0];

  data_t queues[N_IDS-1:0][$];
  int unsigned size;

  function new();
    size = 0;
  endfunction

  // Push a data element to the queue with the given ID.
  function void push(id_t id, data_t data);
    queues[id].push_back(data);
    size++;
  endfunction

  // Determine if the ID queue is empty.
  function bit empty();
    return (size == 0);
  endfunction

  // Pick a non-empty queue at random and return the front element.  Not defined if the ID queue is
  // empty.
  function data_t peek();
    return queues[rand_id()][0];
  endfunction

  // Pick a non-empty queue at random, remove the front element from that queue, and return that
  // element.  Not defined if the ID queue is empty.
  function data_t pop();
    return pop_id(rand_id());
  endfunction

  // Remove the front element of the queue with the given ID and return that element.  Not defined
  // if the queue with the given ID is empty.
  function data_t pop_id(id_t id);
    size--;
    return queues[id].pop_front();
  endfunction

  // Pick a non-empty queue at random and return the ID of that queue.  Not defined if the ID queue
  // is empty.
  function id_t rand_id();
    if (!empty()) begin
      id_t id;
      do begin
        void'(std::randomize(id));
      end while (queues[id].size() == 0);
      return id;
    end else begin
      return 'x;
    end
  endfunction

  // Set the front element of the queue with the given ID.  Not defined if the queue with the given
  // ID is empty; instead use `push()` to insert a new element.
  function void set(id_t id, data_t data);
    queues[id][0] = data;
  endfunction

  // Get the front element of the queue with the given ID.  Not defined if the queue with the given
  // ID is empty.
  function data_t get(id_t id);
    return queues[id][0];
  endfunction

endclass

endpackage

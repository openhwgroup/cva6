// Copyright (c) 2025 Thales DIS design services SAS
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Author: Maxime Colson - Thales
// Date: 17/06/2025
// Contributors:
// Côme Allart - Thales

// This code is designed to decapsulate a RAW format into a csv Trace. It is used to convert them in a human readable format for CI diff. 

#include <array>
#include <chrono>
#include <csignal>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <vector>
#include <string>
#include <array>


const size_t NR_PKT = 20;
const size_t PACKET_SIZE = 40;
const size_t BLOCK_SIZE = NR_PKT * PACKET_SIZE;
typedef unsigned char BYTE;
using packet_t = std::array<BYTE,40>;
typedef std::array<packet_t, NR_PKT> sample_t;

uint64_t extract_bits(const packet_t &packet, std::size_t bit_offset,
                      std::size_t bit_length) { // FIXME add assertion to prevent desynchro segfault
  uint64_t result = 0xdead; // We use 'dead' as an indicator to quickly detect if a desynchro happened during the aquisition (without stoping decapsulation)
  if (bit_length <= 64) {
    result = 0;
    for (std::size_t i = 0; i < bit_length; ++i) {
      std::size_t global_bit = bit_offset + i;
      std::size_t byte_index = global_bit / 8;
      std::size_t bit_index = 7 - (global_bit % 8);
      uint64_t bit = (packet[byte_index] >> bit_index) & 0x1;
      result = (result << 1) | bit;
    }
  }
  return result;
}

template <class T> struct PrintableOption : public std::optional<T> {
  PrintableOption(std::optional<T> &o) : std::optional<T>(o) {}
  PrintableOption(T &v) : std::optional<T>(v) {}
  PrintableOption(uint64_t v) : std::optional<T>(v) {}
  PrintableOption() : std::optional<T>() {}

  friend std::ostream &operator<<(std::ostream &s, const PrintableOption &o) {
    if (o.has_value())
      s << unsigned(*o);
    else
      s << "_";

    return s;
  }
};

struct BitExtractor {
  const packet_t &packet;
  bool is_backward;
  size_t i;

  BitExtractor(const packet_t &packet, bool backward)
      : packet(packet), is_backward(backward),
        i(backward ? PACKET_SIZE * 8 : 0) {}

  uint64_t operator()(size_t bits) { return extract(bits); }
  uint64_t to(size_t bit) { return extract_to(bit); }

  uint64_t extract_to(size_t bit) { return extract(i - bit); }
  uint64_t extract(size_t bits) {
    if (is_backward)
      i -= bits;

    uint64_t result = extract_bits(packet, i, bits);

    if (!is_backward)
      i += bits;

    return result;
  }
};

struct Trace {
    bool                        P_Time; // MSB 
    uint8_t                     P_ID; // 2 bits after MSB 	
    uint8_t                     P_Size; // 5bits after P_ID
    uint64_t                    P_Timestamp; // 64 bits after P_Size
    PrintableOption<uint8_t>    format; // 2bits LSB
    PrintableOption<uint8_t>    subformat; // 2bits before LSB if format=3
    PrintableOption<uint32_t>   address; // start of payload
    PrintableOption<bool>       branch; // F3SF0 (5) F3SF1 (5) else NDF
    PrintableOption<uint8_t>    branches; // F1 (3)
    PrintableOption<uint32_t>   branch_map; // F1 (4 : branches)
    PrintableOption<uint8_t>    branch_count; // NDF
    PrintableOption<uint8_t>    branch_fmt; // NDF
    PrintableOption<uint32_t>   context; // NDF 
    PrintableOption<uint32_t>   ecause; //F3SF1 (8) F3SF1T (70)
    PrintableOption<bool>       ienable; //F3SF3 (5)
    PrintableOption<bool>       encoder_mode;//F3SF3 (6)
    PrintableOption<bool>       interrupt; // F3SF1(9) F3SF1T(71)
    PrintableOption<bool>       irreport; // F2 (5) F1(5)
    PrintableOption<uint8_t>    irdepth; //if call/ret F2(6:2^cal) F1(6:2^cal) else NDF
    PrintableOption<bool>       notify; // F2(3) F1(3)
    PrintableOption<uint32_t>   ioptions; //F3SF3 (8:15)
    PrintableOption<uint8_t>    privilege; // F3SF0 (6) F3SF1 (6) F3SF2 (5)
    PrintableOption<uint8_t>    qual_status;// F3SF3(7)
    PrintableOption<uint64_t>   time; //if time F3SF0(8:72) F3SF1(8:72) F3SF2(7:71) //FIXME encoder could have time in last position 
    PrintableOption<bool>       thaddr; // F3SF1(40) F3SF1_t(104)                
    PrintableOption<uint32_t>   tval; //F3SF1 (41:73) F3SF1_t(105:137) 
    PrintableOption<bool>       updiscon;// F2(4)
    PrintableOption<bool>       denable;// NDF here
    PrintableOption<bool>       dloss;// NDF here
    PrintableOption<uint32_t>   doptions;// NDF here
    uint8_t                     size_branch_map;

  Trace(const packet_t &packet, bool time_flag, bool call_flag) {
    size_branch_map = 0;

    BitExtractor header_extractor(packet, false);
    BitExtractor payload_extractor(packet, true);

    // Header of encapsulated packet :
    P_Time = header_extractor(1);
    P_ID = header_extractor(2);
    P_Size = header_extractor(5);
    size_t P_Start = (PACKET_SIZE - P_Size) * 8;
    P_Timestamp = header_extractor(64);

    // Extraction of fields contained in the payload :
    format = payload_extractor(2);
    if (format == 3) {
      subformat = payload_extractor(2);
    }

    if (format == 3 && subformat.has_value()) {
      switch (subformat.value()) {
      case 0: { // F3SF0
        branch = payload_extractor(1);
        privilege = payload_extractor(2);
        if (time_flag) {
          time = payload_extractor(64);
        }
        address = payload_extractor.to(P_Start);
        break;
      }
      case 1: { // F3SF1
        branch = payload_extractor(1);
        privilege = payload_extractor(2);
        if (time_flag) {
          time = payload_extractor(64);
        }
        ecause = payload_extractor(32);
        interrupt = payload_extractor(1);
        thaddr = payload_extractor(1);
        tval = payload_extractor(32);
        address = payload_extractor.to(P_Start);
        break;
      }
      case 2: { // F3SF2
        privilege = payload_extractor(2);
        if (time_flag) {
          time = payload_extractor(64);
        }
        break;
      }
      case 3: { // F3SF3
        ienable = payload_extractor(1);
        encoder_mode = payload_extractor(1);
        qual_status = payload_extractor(2);
        ioptions = payload_extractor(7);
        break;
      }
      }
    }

    // F2
    if (format == 2) {
      notify = payload_extractor(1);
      updiscon = payload_extractor(1);
      irreport = payload_extractor(1);
      if (call_flag) {                  // FIXME addapt to call_counter_size
        irdepth = payload_extractor(1); // if = 0 else 2^call_counter_size
      }
      address = payload_extractor.to(P_Start);
    }

    // F1
    if (format == 1) {
      branches = payload_extractor(5);
        if (branches == 0) {
        size_branch_map = 31;
      } else if (branches == 1) {
        size_branch_map = 1;
      } else if (branches <= 3) {
        size_branch_map = 3;
      } else if (branches <= 7) {
        size_branch_map = 7;
      } else if (branches <= 15) {
        size_branch_map = 15;
      } else {
        size_branch_map = 31;
      }
      branch_map = payload_extractor(size_branch_map);

      if (branches != 0) {
        notify = payload_extractor(1);
        updiscon = payload_extractor(1);
        irreport = payload_extractor(1);
        if (call_flag) {                  // FIXME addapt to call_counter_size
          irdepth = payload_extractor(1); // if = 0 else 2^call_counter_size
        }
        address = payload_extractor.to(P_Start);
      }
    }
  }

  static std::string csvHeader() {
    return std::string(
        "format,subformat,address,branch,branches,branch_map,branch_count,"
        "branch_fmt,context,ecause,ienable,encoder_mode,interrupt,irreport,"
        "irdepth,notify,ioptions,privilege,qual_status,time,thaddr,tval,"
        "updiscon,denable,dloss,doptions");
  }

  friend std::ostream &operator<<(std::ostream &s, Trace const &trace) {
    trace.put_str(s);
    return s;
  }

  std::ostream &put_str(std::ostream &s) const {
    s << format << "," << subformat << ",";

    s << std::hex << std::nouppercase << address << std::dec << ",";

    s << branch << "," << branches << "," << branch_map << "," << branch_count
      << "," << branch_fmt << ",";

    s << context << "," << ecause << "," << ienable << "," << encoder_mode
      << "," << interrupt << ",";

    s << irreport << "," << irdepth << "," << notify << "," << ioptions << ","
      << privilege << "," << qual_status << ",";

    s << std::hex << std::nouppercase << time << std::dec << ",";

    s << thaddr << "," << tval << "," << updiscon << "," << denable << ","
      << dloss << "," << doptions;

    return s;
  }

  std::string toCSVLine() {
    std::ostringstream oss;
    oss << *this;
    return oss.str();
  }
};

  packet_t hexstr_to_packet(const std::string &hexstr){
    unsigned int byte;
    packet_t packet;
    for (int i=0; i< 40; i++){
      std::sscanf(hexstr.c_str() + 2*i, "%2x",&byte);
      packet[i] = (BYTE) byte;
    }
    return packet;
  }

  std::filesystem::path ext_csv(const std::filesystem::path &pi) {
    auto po = pi ;
    po.replace_extension(".csv");
    return po;
  }

int main(int argc, char* argv[]) {
  if (argc <2){
    std::cerr << "Usage: "<< argv[0] <<" Filepath \n";
    return 1;
  }

  const bool TIME_FLAG = 1;
  const bool CALL_FLAG = 0;
  std::filesystem::path nameFile_i = argv[1];
  std::filesystem::path nameFile_o = ext_csv(nameFile_i);

  std::vector<packet_t> all_packets;
  std::ifstream file_to_extract(nameFile_i);
  std::ofstream csvFile(nameFile_o);
  std::string line;

  while(std::getline(file_to_extract,line)){
    packet_t packet;
    packet=hexstr_to_packet(line);
    all_packets.push_back(packet);
  }

  std::cout << "Number packet read :" << all_packets.size() << std::endl;
  csvFile << Trace::csvHeader() << "\n";
  for (packet_t &packet : all_packets){
    Trace trace(packet, TIME_FLAG, CALL_FLAG);
    csvFile << trace.toCSVLine() << "\n";
  }
  
  return 0;
}
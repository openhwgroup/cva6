// Copyright (c) 2025 Thales DIS design services SAS
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Author: Maxime Colson - Thales
// Date: 17/06/2025
// Contributors:
// Côme Allart - Thales

// This code is designed to receive encapsulated packets emitted by an instruction encoder (See e-trace-encap).
// It captures them in two formats: raw and decapsulated (.csv).
// These files can then be passed to a decoder (e.g., riscv-trace-spec/referenceFlow/scripts/decoder_model.py).

// To properly use this receiver, you need a Digilent FPGA board using the DPTI module from the Adept SDK.

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

#include "dpcdecl.h"
#include "dmgr.h"
#include "dpti.h"

volatile sig_atomic_t stop = 0;

void handle_sigint(int) { stop = 1; }

const size_t NR_PKT = 20;
const size_t PACKET_SIZE = 40;
const size_t BLOCK_SIZE = NR_PKT * PACKET_SIZE;

typedef BYTE packet_t[PACKET_SIZE];
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
      if(branches==0) {
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
      << dloss << "," << doptions ;

    return s;
  }

  std::string toCSVLine() {
    std::ostringstream oss;
    oss << *this;
    return oss.str();
  }
};

std::string getTime () {
  auto now = std::chrono::system_clock::now();
  std::time_t t = std::chrono::system_clock::to_time_t(now);
  std::tm tm = *std::localtime(&t);
  std::ostringstream ts;
  ts << std::put_time(&tm, "%Y%m%d_%H%M");
  std::string timestamp = ts.str();

  return timestamp;
}

void Scan_Device (){
    int indexmax;
  DmgrEnumDevices(&indexmax);
  std::cout << indexmax <<std::endl;
  DVC pdvc;
  for (int i = 0; i<indexmax ; ++i) {
  DmgrGetDvc(i, &pdvc);
  std::cout <<"\n ______________  "<< i << "  _______________\n"<<std::endl;
  std::cout << pdvc.szName << "\n"<<std::endl;
  std::cout << pdvc.szConn <<std::endl;
  }
}

uint32_t init_DPTI(char *board_name, int32_t port) {

  uint32_t peripheral_handle;
  DPRP dprpPti;
  DWORD chunk_size_out; 
  DWORD chunk_size_in; 

  if (!DmgrOpen(&peripheral_handle, board_name)) {
    throw std::runtime_error("Unable to open device");
  }
  if (!DptiGetPortProperties(peripheral_handle, port, &dprpPti)) {
    throw std::runtime_error("Unable to get port properties");
  }
  if (!DptiEnableEx(peripheral_handle, port)) {
    throw std::runtime_error("Unable to enable DPTI");
  }

  DptiSetChunkSize(peripheral_handle, (DWORD) 1 , (DWORD) BLOCK_SIZE);
  DptiGetChunkSize(peripheral_handle, &chunk_size_out, &chunk_size_in);
  std::cout << "Chunk Size out : " << chunk_size_out << "\t Chunk Size in : "<< chunk_size_in ;
  if (dprpPtiAsynchronous & dprpPti) {
    std::cout
        << "\n=================INIT_SUCCESS_ASYNCHRONOUS=================\n";
  }
  if (dprpPtiSynchronous & dprpPti) {
    std::cout
        << "\n=================INIT_SUCCESS_SYNCHRONOUS=================\n";
  }
  return peripheral_handle;
}

std::unique_ptr<sample_t> transaction_DPTI(uint32_t peripheral_handle) {
  bool Transaction;
  int error;
  auto sample_ptr = std::make_unique<sample_t>();
  Transaction = DptiIO(peripheral_handle, NULL, 0, (BYTE *) sample_ptr.get(), BLOCK_SIZE, false);

  if (!Transaction) {
    error = DmgrGetLastError();
    if (error == ercTransferCancelled) {
      throw std::runtime_error("data transfer timed out");
    } else {
      throw std::runtime_error("data transfer failed code : " + std::to_string(error));
    }
  }
  return sample_ptr;
}

int main() {
  // Change this field according to your board / encoder
  char *BOARD_NAME = (char*)"#tpt_0001#ptc_0002#210300075227";
  const int32_t PORT = 1; // 0 or 1
  const bool TIME_FLAG = 1;
  const bool CALL_FLAG = 0;

  uint32_t peripheral_handle;
  peripheral_handle = hifInvalid;
  size_t counter = 0;
  std::vector<std::unique_ptr<sample_t>> all_data;
 //Scan_Device();
  const std::string out_dir = "receiver_data";

  if (!std::filesystem::exists(out_dir)) {
    std::filesystem::create_directory(out_dir);
  }

  std::string timestamp= getTime();

  // File paths
  std::string raw_path = out_dir + "/" + timestamp + "_raw_file.txt";
  std::string csv_path = out_dir + "/" + timestamp + "_data.csv";

  std::ofstream raw_file(raw_path);
  std::ofstream csvFile(csv_path);

  

  // Initialisation of the DPTI Channel
  try {
    peripheral_handle = init_DPTI(BOARD_NAME, PORT);
  } catch (const std::exception &e) {
    if (peripheral_handle != hifInvalid) {
      DptiDisable(peripheral_handle);
      DmgrClose(peripheral_handle);
    }
    std::cerr << "ERROR Init : " << e.what() << std::endl;
    return 1;
  }


  // Capture loop
  signal(SIGINT, handle_sigint);
  std::cout << "\nLoop (Ctrl+C to exit)\n\n";
  auto capture_start = std::chrono::high_resolution_clock::now();
  while (!stop) {
    try {
      auto sample_ptr = transaction_DPTI(peripheral_handle);
      all_data.push_back(std::move(sample_ptr));

      std::cout << "\rIteration : " << counter << "   " << std::flush;
      counter += NR_PKT;
    } catch (const std::exception &e) {
      std::cerr << "ERROR Transaction : " << e.what() << std::endl;
      break;
    }
  }
  auto capture_end = std::chrono::high_resolution_clock::now();

  std::chrono::duration<double> capture_delta_time =
      capture_end - capture_start;
  double capture_delta_time_sec = capture_delta_time.count();
  double throughput = (counter * PACKET_SIZE * 8) / capture_delta_time_sec;
  if (throughput < 1e6) {
    std::cout << "\n\nThroughput : " << std::fixed << std::setprecision(2)
              << throughput / 1e3 << " Kb/s";
  } else {
    std::cout << "\n\nThroughput : " << std::fixed << std::setprecision(2)
              << throughput / 1e6 << " Mb/s";
  }
  std::cout << "\t\tCapturing took :" << capture_delta_time_sec << "s\n";

  // Writing output : Raw / Decapsulated csv
  auto write_start = std::chrono::high_resolution_clock::now();
  if (csvFile.is_open() && raw_file.is_open()) {
    csvFile << Trace::csvHeader() << "\n";
    for (const auto &sample_ptr : all_data) {
      for (const packet_t &packet : *sample_ptr) {
        Trace trace(packet, TIME_FLAG, CALL_FLAG);
        csvFile << trace.toCSVLine() << "\n";
        for (size_t k = 0; k < PACKET_SIZE; ++k) {
          raw_file << std::uppercase << std::hex << std::setw(2)
                   << std::setfill('0') << (unsigned)packet[k];
        }
        raw_file << "\n";
      }
    }
    std::cout
        << "\n========================SUCCESS_WRITE========================\n";
  }
  auto write_end = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> write_delta_time = write_end - write_start;
  double write_delta_time_sec = write_delta_time.count();
  std::cout << "\nWriting Took : " << write_delta_time_sec << "s\n";

  auto raw_size = std::filesystem::file_size(raw_path);
  auto csv_size = std::filesystem::file_size(csv_path);
  std::cout << "\nRaw file size: " << raw_size / 1e6 << " Mbytes\t";
  std::cout << "CSV file size: " << csv_size / 1e6 << " Mbytes\n";

  DptiDisable(peripheral_handle);
  DmgrClose(peripheral_handle);

  std::cout
      << "\n========================SUCCESS_CLOSE========================\n\n";

  return 0;
}
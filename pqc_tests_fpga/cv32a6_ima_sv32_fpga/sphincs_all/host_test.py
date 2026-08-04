import serial
import sys

# User configs
PORT = '/dev/ttyUSB0'
BAUD_RATE = 57600

def run_kyber_test():
    try:
        # Open serial port
        print(f"Opening {PORT} at {BAUD_RATE} baud...")
        ser = serial.Serial(PORT, BAUD_RATE, timeout=1.0)
        
        print("Waiting for FPGA to initialize...")
        
        while True:
            line = ser.readline().decode('utf-8', errors='ignore').strip()
            if line:
                print(f"FPGA: {line}")
            
            if "Waiting for trigger" in line:
                break
                
        print("\nTriggering SHPHINCS+ test on FPGA...")
        ser.write(b'c')
        
        print("\n--- Test Output ---")
        while True:
            line = ser.readline().decode('utf-8', errors='ignore').strip()
            if line:
                print(line)
                
            # Stop reading once the test completes or fails
            if "ALL TESTS PASSED" in line or "TEST FAILED" in line:
                # Read any remaining lines until the 1-second timeout hits
                while True:
                    extra_line = ser.readline().decode('utf-8', errors='ignore').strip()
                    if not extra_line: # An empty string means the timeout was reached
                        break
                    print(extra_line)
                break
                
    except serial.SerialException as e:
        print(f"Serial Error: {e}")
    except KeyboardInterrupt:
        print("\nHost script terminated by user.")
    finally:
        if 'ser' in locals() and ser.is_open:
            ser.close()
            print("\nSerial connection closed.")

if __name__ == "__main__":
    run_kyber_test()
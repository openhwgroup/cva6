import serial
import struct
import time

SERIAL_PORT = "/dev/ttyUSB0" 
BAUD_RATE = 57600

def main():
    try:
        print(f"Opening {SERIAL_PORT} at {BAUD_RATE} baud...")
        with serial.Serial(SERIAL_PORT, BAUD_RATE, timeout=5) as ser:
            
            print("Waiting for FPGA to initialize...")
            
            while True:
                line = ser.readline().decode('utf-8', errors='ignore').strip()
                if line:
                    print(f"FPGA says: {line}")
                if "Awaiting data" in line:
                    break

            a = 1500
            b = 3500
            print(f"\nSending a={a}, b={b} as raw 32-bit binary bytes...")
            
            ser.write(struct.pack('<I', a))
            ser.write(struct.pack('<I', b))
            
            print("Waiting for computation result...")
            
            result = ser.readline().decode('utf-8', errors='ignore').strip()
            print(f"\n--- Returned: {result} ---")
            
    except serial.SerialException as e:
        print(f"Serial Error: {e}")
        print(f"Make sure {SERIAL_PORT} is correct, the FPGA is running via GDB, and you have dialout permissions.")
    except KeyboardInterrupt:
        print("\nTest aborted by user.")

if __name__ == "__main__":
    main()
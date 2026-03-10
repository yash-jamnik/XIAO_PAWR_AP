import serial

# Change COM port and baudrate as needed
PORT = 'COM8'
BAUDRATE = 115200
DEFAULT_COMMAND = '[+]join,9999\r\n'

ser = serial.Serial(PORT, BAUDRATE, timeout=1)

try:
    while True:
        user_cmd = input("Type UART command (or 'exit' to quit): ")
        if user_cmd.lower() == 'exit':
            break
        # Ensure command ends with CRLF
        if not user_cmd.endswith('\r\n'):
            user_cmd += '\r\n'
        ser.write(user_cmd.encode('utf-8'))
        print(f"Sent: {user_cmd.strip()}")
        # Send default command after each input
        ser.write(DEFAULT_COMMAND.encode('utf-8'))
        print(f"Sent default: {DEFAULT_COMMAND.strip()}")
except KeyboardInterrupt:
    pass
finally:
    ser.close()
    print("Serial port closed.")

import sys
import spilib

# Initialize Cheetah SPI/USB adapter
spi = spilib.SpiComm()

# Send some data to the slave
sys.stdout.write("Sending data to slave...");
spi.SendToSlave([0xFF, 0xF0, 0x33, 0x55, 0x12, 0x34, 0x56, 0x53, 0x9A])
sys.stdout.write("done!")

# Receive some data from the slave
recvData = spi.RecvFromSlave(4096)
sys.stdout.write("Received data from slave:\n")
for recvByte in recvData:
  sys.stdout.write("%x " % recvByte)
sys.stdout.write("\nDone!\n")

# Close and exit
sys.stdout.write("Exiting...\n")
sys.exit(0)


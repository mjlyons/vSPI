from cheetah_py import *
from time import *

def print_usage():
  print \
"""
usage: spitest.py PORT
"""

if (len(sys.argv) < 2):
  print_usage()
  sys.exit(1)

port      = int(sys.argv[1])
mode      = 2
bitrate   = 40000  # kbps
byteCount = 11   # bytes

# Open the device
handle = ch_open(port)
if (handle <= 0):
  print "Unable to open Cheetah device on port %d" % port
  print "Error code = %d (%s)" % (handle, ch_status_string(handle))
  sys.exit(1)

print "Opened Cheetah device on port %d" % port

ch_host_ifce_speed_string = ""
if (ch_host_ifce_speed(handle)):
  ch_host_ifce_speed_string = "high speed"
else:
  ch_host_ifce_speed_string = "full speed"
print "Host interface is %s" % ch_host_ifce_speed_string

# Ensure that SPI subsystem is configured
ch_spi_configure(handle, (mode >> 1), mode & 1, CH_SPI_BITORDER_MSB, 0x0)
print "SPI configuration set to mode %d, MSB shift, SS[2:0] active low" % mode
sys.stdout.flush()

# Set the bitrate
bitrate = ch_spi_bitrate(handle, bitrate)
print "Bitrate set to %d kHz" % bitrate
sys.stdout.flush()

# Create 4KB of fake data so we can exchange it for real data
data_in = array('B', [0 for i in range(byteCount)])
ch_spi_queue_clear(handle)
ch_spi_queue_oe(handle, 1)
ch_spi_queue_ss(handle, 0x1)

ch_spi_queue_byte(handle, 1, 1)    # Sending data to FPGA
ch_spi_queue_byte(handle, 1, 0xFF)   # Sending bytes
ch_spi_queue_byte(handle, 1, 0xF0)   # Sending bytes
ch_spi_queue_byte(handle, 1, 0x33)   # Sending bytes
ch_spi_queue_byte(handle, 1, 0x55)   # Sending bytes
ch_spi_queue_byte(handle, 1, 0x12)   # Sending bytes
ch_spi_queue_byte(handle, 1, 0x34)   # Sending bytes
ch_spi_queue_byte(handle, 1, 0x56)   # Sending bytes
ch_spi_queue_byte(handle, 1, 0x78)   # Sending bytes
ch_spi_queue_byte(handle, 1, 0x9A)   # Sending bytes

ch_spi_queue_ss(handle, 0)

#ch_spi_queue_byte(handle, 1, 0x00) # Send an empty byte, SS high


(actualByteCount, data_in) = ch_spi_batch_shift(handle, byteCount)

#if (actualByteCount < 0):
#  print "error: %s" % ch_status_string(count)
#elif (actualByteCount != byteCount):
#  print "error: read %d bytes (expected %d)" % (actualByteCount, byteCount)
#else:
for i in range(actualByteCount):
  sys.stdout.write("%d " % data_in[i])
sys.stdout.write("\n")

# Close and exit
ch_close(handle)
sys.exit(0)


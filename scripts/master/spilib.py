from cheetah_py import *

class SpiComm:
  """Controls a Cheetah USB/SPI adapter to talk over SPI to the spiifc
  module"""
  
  _port = 0         # Change if using multiple Cheetahs
  _mode = 3         # spiifc SPI mode
  _bitrate = 30000  # bytes

  handle = None     # handle to Cheetah SPI

  class SpiCommError(Exception):
    """There was some error interacting with the Cheetah SPI adapter"""
    def __init__(self, msg):
      self.msg = msg

  def __init__(self):
    self.handle = ch_open(self._port)
    if (self.handle <= 0):
      raise SpiCommError("Unable to open Cheetah device on port %d.\nError code = %d (%s)" % (self._port, self.handle, ch_status_string(self.handle)))
    ch_host_ifce_speed(self.handle)
    ch_spi_configure(self.handle, (self._mode >> 1), self._mode & 1, 
        CH_SPI_BITORDER_MSB, 0x0)
    ch_spi_bitrate(self.handle, self._bitrate)

  def __del__(self):
    ch_close(self.handle)

  def SendToSlave(self, byteArray):
    byteCount = len(byteArray) + 1
    data_in = array('B', [0 for i in range(byteCount)])
    actualByteCount = 0
    ch_spi_queue_clear(self.handle)
    ch_spi_queue_oe(self.handle, 1)
    ch_spi_queue_ss(self.handle, 0x1)
    ch_spi_queue_byte(self.handle, 1, 1)     # Sending data to slave
    for byte in byteArray:
      ch_spi_queue_byte(self.handle, 1, byte)
    ch_spi_queue_ss(self.handle, 0)
    (actualByteCount, data_in) = ch_spi_batch_shift(self.handle, byteCount)
    
  def RecvFromSlave(self, byteCount):
    totalByteCount = byteCount + 1          # Extra byte for cmd
    data_in = array('B', [0 for i in range(totalByteCount)])
    actualByteCount = 0
    ch_spi_queue_clear(self.handle)
    ch_spi_queue_oe(self.handle, 1)
    ch_spi_queue_ss(self.handle, 0x1)
    ch_spi_queue_byte(self.handle, 1, 3)    # Receive data from slave
    for byteIndex in range(byteCount):
      ch_spi_queue_byte(self.handle, 1, 0)
    ch_spi_queue_ss(self.handle, 0)
    (actualByteCount, data_in) = ch_spi_batch_shift(self.handle,
        totalByteCount)
    return data_in


{-# LANGUAGE DeriveDataTypeable #-}
module Network.NBD.Data where

import           Control.Exception.Base (Exception)
import           Data.Bits
import           Data.Typeable (Typeable)
import           GHC.Word
import           NbdAPI

{-# ANN module ("HLint: ignore Use camelCase"::String) #-}

-- Represent NBD data and constants

nbd_INIT_PASSWD :: Word64
nbd_INIT_PASSWD = 0x4e42444d41474943

nbd_NEW_MAGIC :: Word64
nbd_NEW_MAGIC = 0x49484156454F5054

nbd_FLAG_FIXED_NEWSTYLE :: Bits a => a
nbd_FLAG_FIXED_NEWSTYLE = bit 0

nbd_FLAG_C_FIXED_NEWSTYLE :: Bits a => a
nbd_FLAG_C_FIXED_NEWSTYLE = bit 0

nbd_OPT_REPLY_MAGIC :: Word64
nbd_OPT_REPLY_MAGIC = 0x0003e889045565a9

nbd_REP_ACK :: Word32
nbd_REP_ACK = 0x00000001

nbd_REP_ERR_UNSUP :: Word32
nbd_REP_ERR_UNSUP = 0x80000001

data ProtocolException =
  InvalidClientFlags !Word32
  | InvalidMagic String !Word64
  deriving (Show, Typeable)

instance Exception ProtocolException

data NbdOption = ExportName
               | Abort
               | ListExports
               | UnknownOption Word32
  deriving (Show, Eq)

instance Enum NbdOption where
  toEnum n = case n of
    1 -> ExportName
    2 -> Abort
    3 -> ListExports
    v -> UnknownOption $ fromIntegral v

  fromEnum a = case a of
    ExportName -> 1
    Abort -> 2
    ListExports -> 3
    UnknownOption v -> fromIntegral v

nbd_C_OPT_MAGIC :: Word64
nbd_C_OPT_MAGIC = 0x49484156454F5054 -- same as nbd_NEW_MAGIC

nbd_FLAG_HAS_FLAGS :: Bits a => a
nbd_FLAG_HAS_FLAGS = bit 0

nbd_FLAG_SEND_FLUSH :: Bits a => a
nbd_FLAG_SEND_FLUSH = bit 2

-- Handle is a Word64, defined by extraction
type ByteCount = Int
type FileOffset = Int

nbd_REQUEST_MAGIC :: Word32
nbd_REQUEST_MAGIC = 0x25609513

nbd_REPLY_MAGIC :: Word32
nbd_REPLY_MAGIC = 0x67446698

-- request constants
nbd_CMD_READ :: Word16
nbd_CMD_READ = 0

nbd_CMD_WRITE :: Word16
nbd_CMD_WRITE = 1

nbd_CMD_DISC :: Word16
nbd_CMD_DISC = 2

nbd_CMD_FLUSH :: Word16
nbd_CMD_FLUSH = 3

errCode :: ErrorCode -> Word32
errCode err = case err of
  ESuccess -> 0
  EInvalid -> 22
  ENospc -> 28

{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_formal_types (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,0,0,1] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "D:\\sources\\haskell\\.stack-work\\install\\b4553662\\bin"
libdir     = "D:\\sources\\haskell\\.stack-work\\install\\b4553662\\lib\\x86_64-windows-ghc-8.6.5\\formal-types-0.0.0.1-LNuWVcA3B6I9n93ajhqv14"
dynlibdir  = "D:\\sources\\haskell\\.stack-work\\install\\b4553662\\lib\\x86_64-windows-ghc-8.6.5"
datadir    = "D:\\sources\\haskell\\.stack-work\\install\\b4553662\\share\\x86_64-windows-ghc-8.6.5\\formal-types-0.0.0.1"
libexecdir = "D:\\sources\\haskell\\.stack-work\\install\\b4553662\\libexec\\x86_64-windows-ghc-8.6.5\\formal-types-0.0.0.1"
sysconfdir = "D:\\sources\\haskell\\.stack-work\\install\\b4553662\\etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "formal_types_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "formal_types_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "formal_types_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "formal_types_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "formal_types_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "formal_types_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "\\" ++ name)

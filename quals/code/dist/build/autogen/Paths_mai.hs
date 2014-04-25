module Paths_mai (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch


version :: Version
version = Version {versionBranch = [0,1,0,0], versionTags = []}
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/david/.cabal/bin"
libdir     = "/Users/david/.cabal/lib/x86_64-osx-ghc-7.8.1/mai-0.1.0.0"
datadir    = "/Users/david/.cabal/share/x86_64-osx-ghc-7.8.1/mai-0.1.0.0"
libexecdir = "/Users/david/.cabal/libexec"
sysconfdir = "/Users/david/.cabal/etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "mai_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "mai_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "mai_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "mai_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "mai_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)

{-|
Module      : Main
Description : Golden tests: run checkProofs over every example and compare with stored output
License     : MIT
-}
module Main (main) where

import Control.Exception (SomeException, displayException, try)
import Control.Monad (forM, when)
import Data.List (sort)
import System.Directory
    ( createDirectoryIfMissing
    , doesFileExist
    , getDirectoryContents
    )
import System.Environment (getArgs, lookupEnv)
import System.Exit (ExitCode (..), exitWith)
import System.FilePath ((<.>), (</>), takeBaseName, takeExtension)
import System.IO (BufferMode (LineBuffering), hPutStrLn, hSetBuffering, stderr, stdout)

import CheckProofs (checkProofsReport)

-- | All paths are relative to the package root (cabal runs tests from there)
examplesDir :: FilePath
examplesDir = "examples"

goldenDir :: FilePath
goldenDir = "test" </> "golden"

-- | The checker writes its detailed log here
logsDir :: FilePath
logsDir = "logs"

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  args <- getArgs
  updateEnv <- lookupEnv "GOLDEN_UPDATE"
  let update = "--accept" `elem` args || updateEnv == Just "1"
  mapM_ (createDirectoryIfMissing True) [logsDir, goldenDir]
  examples <- sort . filter ((== ".hs") . takeExtension)
    <$> getDirectoryContents examplesDir
  when (null examples) $ do
    hPutStrLn stderr $ "No .hs files found in " ++ examplesDir
    exitWith (ExitFailure 2)
  results <- forM examples (runGolden update)
  let failed = [name | (name, False) <- results]
  putStrLn ""
  putStrLn $ "Golden tests: " ++ show (length results - length failed)
    ++ " passed, " ++ show (length failed) ++ " failed."
  if null failed
    then putStrLn "All golden tests passed."
    else do
      mapM_ (hPutStrLn stderr . ("FAIL " ++)) failed
      hPutStrLn stderr $ "Golden files live in " ++ goldenDir
        ++ ". If the change is intentional, regenerate them with"
        ++ " `cabal run golden-tests -- --accept`"
        ++ " (or GOLDEN_UPDATE=1 cabal test)."
      exitWith (ExitFailure 1)

-- | Run the checker for one example and compare with (or write) its golden file
runGolden :: Bool -> FilePath -> IO (FilePath, Bool)
runGolden update example = do
  putStrLn $ "=== " ++ example
  actual <- runChecker example
  let goldenFile = goldenDir </> takeBaseName example <.> "txt"
  exists <- doesFileExist goldenFile
  if update || not exists
    then do
      writeFile goldenFile actual
      putStrLn $ "    " ++ (if exists then "UPDATED" else "CREATED") ++ " " ++ goldenFile
      return (example, True)
    else do
      expected <- readFile goldenFile
      if expected == actual
        then do
          putStrLn "    OK"
          return (example, True)
        else do
          reportDiff goldenFile expected actual
          return (example, False)

-- | Run the checker, turning a crash into text so it can be golden-tested too
runChecker :: FilePath -> IO String
runChecker example = do
  r <- try (checkProofsReport (examplesDir </> example))
  return $ case r of
    Right out -> out
    Left e -> "<<EXCEPTION>>\n" ++ displayException (e :: SomeException) ++ "\n"

-- | Point at the first differing line between golden and actual output
reportDiff :: FilePath -> String -> String -> IO ()
reportDiff goldenFile expected actual = do
  putStrLn $ "    FAIL: output differs from golden file " ++ goldenFile
  let expLines = lines expected
      actLines = lines actual
      common = min (length expLines) (length actLines)
  case [i | i <- [0 .. common - 1], expLines !! i /= actLines !! i] of
    (i:_) -> do
      putStrLn $ "    first difference at line " ++ show (i + 1) ++ ":"
      putStrLn $ "      golden: " ++ show (expLines !! i)
      putStrLn $ "      actual: " ++ show (actLines !! i)
    [] ->
      putStrLn $ "    common prefix matches, but lengths differ: golden has "
        ++ show (length expLines) ++ " lines, actual has "
        ++ show (length actLines) ++ " lines"

module Main (main) where

import System.Environment (getArgs)
import GenSmsPdu

tr "normal" = Normal
tr "c"      = GenC
tr "send"   = Send
tr _        = Normal

main = do args <- getArgs
          mapM_ test_suite (map tr (args ++ ["c"]))

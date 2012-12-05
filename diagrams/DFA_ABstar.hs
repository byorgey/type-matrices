{-# LANGUAGE NoMonomorphismRestriction #-}

import Diagrams.Prelude
import Diagrams.Backend.Cairo.CmdLine

node x = text (show x) <> circle 1

dfaNodes = node 1 # named "1" ||| strutX 3 ||| node 2 # named "2"

-- wait until we implement better built-in support for arrows in
-- diagrams (soon)

main = defaultMain dfaNodes
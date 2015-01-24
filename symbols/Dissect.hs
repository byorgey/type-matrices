{-# LANGUAGE NoMonomorphismRestriction #-}

import Diagrams.Backend.Cairo.CmdLine
import Diagrams.Prelude

ht = 1.2
dissect = triangle 1 # scaleToY ht # alignB <> vrule ht # alignB

main = defaultMain (dissect # frame 0.05)

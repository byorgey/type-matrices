{-# LANGUAGE NoMonomorphismRestriction #-}

import Diagrams.Backend.Cairo.CmdLine
import Diagrams.Prelude

ht = 1.2
jokers = strokeTrail $ fromOffsets [0.5 *^ unitX, (-0.5) ^& ht]

main = defaultMain (jokers # frame 0.05)

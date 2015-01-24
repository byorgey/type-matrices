{-# LANGUAGE NoMonomorphismRestriction #-}

import Diagrams.Backend.Cairo.CmdLine
import Diagrams.Prelude

ht = 1.2
clowns = strokeTrail $ fromOffsets [0.5 *^ unit_X, 0.5 ^& ht]

main = defaultMain (clowns # frame 0.05)

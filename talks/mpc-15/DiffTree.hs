import           Data.Tree
import           Diagrams.Backend.PGF.CmdLine
import           Diagrams.Prelude
import           TypeMatricesDiagrams

t = Nothing ##
    [ Nothing ##
      [ Nothing ##
          leaves [ Just A, Just A ]
      , leaf $ Just A
      ]
    , Nothing ##
      [ Nothing ##
        [ leaf $ Just A
        , Nothing ## leaves [Just H, Just A]
        ]
      , Nothing ## leaves [Just A, Just A]
      ]
    ]
  where (##)   = Node
        leaf x = Node x []
        leaves = map leaf

dia = renderT t # frame 0.5

main = mainWith dia

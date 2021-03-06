import           Development.Shake
import           Development.Shake.FilePath

lhs2TeX, pdflatex, mklatex :: String
lhs2TeX  = "lhs2TeX"
pdflatex = "pdflatex"
mklatex  = "mklatex"

main :: IO ()
main = shake shakeOptions $ do

    want ["type-matrices-mpc-15.pdf"]

    "*.tex" *> \output -> do
      let input = output -<.> "lhs"
      need [input]
      cmd lhs2TeX $ ["--poly", "-o", output, input]

    "*.pdf" *> \output -> do
      let input = replaceExtension output "tex"
      hsFiles <- getDirectoryFiles "" ["*.hs"]
      need (input : hsFiles)
      cmd pdflatex $ ["--enable-write18", input]

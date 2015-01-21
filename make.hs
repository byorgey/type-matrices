import           Development.Shake
import           Development.Shake.FilePath

lhs2TeX, pdflatex, latexmk :: String
lhs2TeX  = "lhs2TeX"
pdflatex = "pdflatex"
latexmk  = "latexmk"

main :: IO ()
main = shake shakeOptions $ do

    want ["type-matrices.pdf"]

    "*.tex" *> \output -> do
        let input = replaceExtension output "lhs"
        need [input]
        cmd lhs2TeX $ ["-o", output] ++ [input]

    "*.pdf" *> \output -> do
        let input = replaceExtension output "tex"
        need [input]
        () <- cmd pdflatex $ ["--enable-write18", input]
        cmd latexmk $ ["-pdf", input]

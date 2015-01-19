import           Development.Shake
import           Development.Shake.FilePath

lhs2TeX, pdflatex, rubber :: String
lhs2TeX  = "lhs2TeX"
pdflatex = "pdflatex"
rubber   = "rubber"

main :: IO ()
main = shake shakeOptions $ do

    want ["type-matrices.pdf"]

    "*.tex" *> \output -> do
        let input = replaceExtension output "lhs"
        need [input]
        cmd lhs2TeX $ ["-o", output] ++ [input]

    -- In general, running LaTeX enough times to resolve everything
    -- requires parsing the output of LaTeX.  A nice tool that can do
    -- this automatically is "rubber".  If you have (or can install)
    -- rubber then this ought to work.  Otherwise we'll have to go
    -- with the tried and true "just run LaTeX twice no matter what".
    "*.pdf" *> \output -> do
        let input = replaceExtension output "tex"
        need [input]
        () <- cmd pdflatex $ ["--enable-write18", input]
        cmd rubber $ ["-f", "-d", input]

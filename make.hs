import Development.Shake
import Development.Shake.FilePath

lhs2TeX = "/Users/dpiponi/Library/Haskell/bin/lhs2TeX"
pdflatex = "/usr/texbin/pdflatex"

main = shake shakeOptions $ do

    want ["type-matrices.pdf"]

    "*.tex" *> \output -> do
        let input = replaceExtension output "lhs"
        need [input]
        system' lhs2TeX $ ["-o", output] ++ [input]

    -- How many times do I need to run latex
    -- to resolve xrefs. Is there a clever trick using
    -- Shake to deal with this?
    "*.pdf" *> \output -> do
        let input = replaceExtension output "tex"
        need [input]
        system' pdflatex $ [input]

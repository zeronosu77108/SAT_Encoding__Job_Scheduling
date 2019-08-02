inputfile = ARGS[1]
outputfile = replace(inputfile, "txt" => "sat")
enfile = replace(inputfile, "txt" => "repl")

codes = open(f-> read(f, String), inputfile)

s = unique(split( replace(codes, "-" => ""), [' ','\n'], keepempty=false))

enf = open(enfile, "w")

x = 1
for el in s
    global x,codes

    codes = replace(codes, el => x)
    println(enf, "$x $el")

    x += 1
end
close(enf)

codes = replace(codes, r"^\ *\n"m => "")
codes = replace(codes, "\n" => " 0\n")

outf = open(outputfile, "w")
print(outf, codes)
close(outf)

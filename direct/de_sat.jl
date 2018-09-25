inputfile = ARGS[1]
outputfile = replace(inputfile, "output" => "ans")
enfile = replace(inputfile, "_output.txt" => ".repl")

repl = []

open( enfile , "r" ) do fp
	for line in eachline(fp)
		append!( repl, [split(line, " ")[2]])
	end
end

# println(repl)
codes = open( f-> read(f, String), inputfile)
codes = replace(codes, " " => "\n")


for i in length(repl):-1:1
	global codes
# 	println( string(i))
	codes = replace(codes, "$(string(i))\n" => "$(repl[i])\n")
end

println(codes)

# x = 1
# for el in s
#     global x,codes

#     codes = replace(codes, el => x)
#     println(enf, "$x $el")

#     x += 1
# end
# close(enf)

# codes = replace(codes, "\n" => " 0\n")

# outf = open(outputfile, "w")
# print(outf, codes)
# close(outf)
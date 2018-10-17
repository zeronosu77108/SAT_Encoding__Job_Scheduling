using Printf

n = 3
m = 3
variables = ["m"]
cond = []

numbers = Dict{String,Int}()
num_count = 0


satfile = "scheduling_log.sat"
replfile = "scheduling_log.repl"

for i in 0:(n-1), j in 1:m
	push!(variables, @sprintf("s_%d",m*i+j))
end

for i in 0:(n-1), j in 1:n, k in (j+1):m
	tmp = [i*m+j , i*m+k ]
	push!(cond,tmp)
end

for i in 1:m, j in 0:(n-1), k in (j+1):(n-1)
	tmp = [m*j+i, m*k+i]
	push!(cond,tmp)
end


max = 17
max_b = Integer(round(log(2,max)))
# max = 2^max_b

p = [5,8,4,5,4,6,6,5,5]
# p = [55,30,20,10,62,32,27,30,48]
# p = [661,6,333,  168,489,343,  171,505,324]
# p = [4, 1, 9, 9, 4, 8, 2, 8, 6, 1, 7, 5, 4, 9, 6]


function out_repl()
	replf = open(replfile, "w")
	# key = keys(numbers)
	for k in sort(collect(numbers), by = tuple -> last(tuple), rev=false)
		println(replf, "$(k[2]) $(k[1])")
		# println(replf, "$(numbers[k]) $(k)")
	end
	close(replf)
end


function get_number(s::String)
	global numbers
	global num_count

	if haskey(numbers, s) == false
		num_count += 1
		numbers[s] = num_count
	end

	return numbers[s] 
end


function print_cond()
	satf = open(satfile, "w")
	tseitin_count = 1

	for v in variables
		for i in 0:max_b
			get_number("$v^{($i)}")
		end

		for i in (max+1):(2^(max_b+1)-1)
			for j in 0:(max_b)
				if ((i >> j) & 1 == 1)
					print(satf, "-", get_number("$v^{($j)}"), " ")
				end
			end
			println(satf, "0")
		end
	end

	for v in variables
		for i in 0:max_b
			get_number("c_{$v^{($i)}}")
		end
	end


	for i in 1:(n*m)
		println(satf, "-", get_number("s_$i^{($max_b)}"), " ",
									"-", get_number("c_{s_$i^{($max_b)}}"), " 0")

		println(satf, get_number("m^{($max_b)}"), " ",
									"-", get_number("s_$i^{($max_b)}"), " 0")

		print(satf, get_number("m^{($max_b)}"), " ",
								"-", get_number("c_{s_$i^{($max_b)}}"), " 0")	

		
		for j in (max_b-1):-1:0
			print(satf, get_number("a"^tseitin_count), " ")
			println(satf, get_number("a"^(tseitin_count+1)), " 0")
			if (p[i] >> (j+1) & 1 == 1)
				println(satf, "-", get_number("a"^(tseitin_count)), " 0")
			else
				println(satf, "-", get_number("a"^(tseitin_count)), " ",
											"-", get_number("m^{($(j+1))}"), " 0")
				println(satf, "-", get_number("a"^(tseitin_count)), " ",
											get_number("s_$i^{($(j+1))}"), " 0")
				println(satf, "-", get_number("a"^(tseitin_count)), " ",
											get_number("c_{s_$i^{($(j+1))}}"))
			end

			if (p[i] >> j & 1 == 1)
				println(satf, "-", get_number("a"^(tseitin_count+1)), " ",
											get_number("s_$i^{($j)}"), " ", 
											get_number("m^{($j)}"), " ",
											get_number("c_{s_$i^{($(j+1))}}"), " 0")

				println(satf, "-", get_number("a"^(tseitin_count+1)), " ",
											get_number("s_$i^{($j)}"), " ",
											"-", get_number("c_{s_$i^{($j)}}"), " ",
										  get_number("c_{s_$i^{($(j+1))}}"), " 0")

				println(satf, "-", get_number("a"^(tseitin_count+1)), " ",
											"-", get_number("s_$i^{($j)}"), " ",
											get_number("c_{s_$i^{($j)}}"), " ",
											get_number("c_{s_$i^{($(j+1))}}"), " 0")

				println(satf, "-", get_number("a"^(tseitin_count+1)), " ",
											"-", get_number("s_$i^{($j)}"), " ",
											"-", get_number("c_{s_$i^{($j)}}"), " ",
											get_number("m^{($j)}"), " 0")

				println(satf, "-", get_number("a"^(tseitin_count+1)), " ",
											"-", get_number("s_$i^{($j)}"), " ",
											"-", get_number("c_{s_$i^{($j)}}"), " ",
											get_number("c_{s_$i^{($(j+1))}}"), " 0")

			else
				println(satf, "-", get_number("a"^(tseitin_count+1)), " ",
											"-", get_number("s_$i^{($j)}"), " ",
											"-", get_number("c_{s_$i^{($j)}}"), " ",
											get_number("c_{s_$i^{($(j+1))}}"), " 0")

				println(satf, "-", get_number("a"^(tseitin_count+1)), " ",
											"-", get_number("s_$i^{($j)}"), " ",
											get_number("m^{($j)}"), " ",
											get_number("c_{s_$i^{($(j+1))}}"), " 0")

				println(satf, "-", get_number("a"^(tseitin_count+1)), " ",
											"-", get_number("c_{s_$i^{($j)}}"), " ",
											get_number("m^{($j)}"), " ",
											get_number("c_{s_$i^{($(j+1))}}"), " 0")
			end
			tseitin_count += 2
		end
		
	end

	for c in cond
		# print(get_number(string(tseitin_count)), " ")
		# println(get_number(string(tseitin_count+1)), " 0")

		# if (p[i] >> max_b & 1 == 0)
		# 	print("-", get_number(string(tseitin_count)), " ")
		# 	println("-", get_number("m^{($(j+1))}"), " 0")

		# 	print("-", get_number(string(tseitin_count)), " ")
		# 	println("-", get_number("s_$i^{($(j+1))}"), " 0")

		# 	print("-", get_number(string(tseitin_count)), " ")
		# 	println("-", get_number("c_{s_$i^{($(j+1))}}"), " 0")

		# else
		# 	println("-", get_number(string(tseitin_count)), " 0")
		# end

		# for j in (max_b-1):-1:0
		# 	if (p[i] >> j & 1 == 1)
		# 		# print("-", get_number(string(tseitin_count+1)), " ")
		# 		print(get_number("s_$i^{($j)}"), " ")
		# 		print(get_number("m^{($j)}"), " ")
		# 		println(get_number("c_{s_$i^{($(j+1))}}"), " 0")

		# 		# print("-", get_number(string(tseitin_count+1)), " ")
		# 		print(get_number("s_$i^{($j)}"), " ")
		# 		print("-", get_number("c_{s_$i^{($j)}}"), " ")
		# 		println(get_number("c_{s_$i^{($(j+1))}}"), " 0")

		# 		# print("-", get_number(string(tseitin_count+1)), " ")
		# 		print("-", get_number("s_$i^{($j)}"), " ")
		# 		print(get_number("c_{s_$i^{($j)}}"), " ")
		# 		println(get_number("c_{s_$i^{($(j+1))}}"), " 0")

		# 		# print("-", get_number(string(tseitin_count+1)), " ")
		# 		print("-", get_number("s_$i^{($j)}"), " ")
		# 		print(get_number("c_{s_$i^{($j)}}"), " ")
		# 		println(get_number("m^{($j)}"), " 0")

		# 		# print("-", get_number(string(tseitin_count+1)), " ")
		# 		print("-", get_number("s_$i^{($j)}"), " ")
		# 		print("-", get_number("c_{s_$i^{($j)}}"), " ")
		# 		println(get_number("c_{s_$i^{($(j+1))}}"), " 0")

		# 	else
		# 		print("-", get_number("s_$i^{($j)}"), " ")
		# 		print("-", get_number("c_{s_$i^{($j)}}"), " ")
		# 		println(get_number("c_{s_$i^{($(j+1))}}"), " 0")

		# 		print("-", get_number("s_$i^{($j)}"), " ")
		# 		print(get_number("m^{($j)}"), " ")
		# 		println(get_number("c_{s_$i^{($(j+1))}}"), " 0")

		# 		print("-", get_number("c_{s_$i^{($j)}}"), " ")
		# 		print(get_number("m^{($j)}"), " ")
		# 		println(get_number("c_{s_$i^{($(j+1))}}"), " 0")
		# 	end
		# end
	end
	close(satf)
end

print_cond()
out_repl()

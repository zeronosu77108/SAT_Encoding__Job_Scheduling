using Printf

n = 3
m = 3
variables = ["m"]
cond = []

numbers = Dict{String,Int}()
num_count = 0

satfile = "scheduling_direct.sat"
replfile = "scheduling_direct.repl"

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

	for v in variables
		for i in 0:max
			print(satf, @sprintf "%d " get_number("p($v=$i)"))
		end
		println(satf, "0")


		for i in 0:max
			for j in (i+1):max
				print(  satf, @sprintf "-%d " get_number("p($v=$i)"))
				println(satf, @sprintf "-%d 0" get_number("p($v=$j)"))
			end
		end
	end

	for i in 1:(n*m)
		for j in 0:max
			if j < p[i]
				println(satf, @sprintf "-%d 0" get_number("p(m=$j)"))
			else
				for k in (j-p[i]+1):max
					print(  satf, @sprintf "-%d " get_number("p(m=$j)"))
					println(satf, @sprintf "-%d 0" get_number("p(s_$i=$k)"))
				end
			end
		end
	end

	for c in cond
		print(  satf, @sprintf "%d "  get_number("q_{$(c[1]),$(c[2])}"))
		println(satf, @sprintf "%d 0" get_number("q_{$(c[2]),$(c[1])}"))


		for i in 0:max
			if i < p[ c[2] ]
				println(satf, @sprintf "-%d -%d 0" get_number("q_{$(c[1]),$(c[2])}") get_number("p(s_$(c[1])=$i)"))
			else
				for j in (i-p[c[2]]+1):max
					print(satf, @sprintf "-%d" get_number("q_{$(c[1]),$(c[2])}"))
					println(satf, @sprintf "-%d -%d 0" get_number("p(s_$(c[1])=$i)") get_number("p(s_$(c[2])=$j)"))
				end
			end
		end

		for i in 0:max
			if i < p[ c[1] ]
				println(satf, @sprintf "-%d -%d 0" get_number("q_{$(c[2]),$(c[1])}") get_number("p(s_$(c[2])=$i)"))
			else
				for j in (i-p[c[1]]+1):max
					print(satf, @sprintf "-%d" get_number("q_{$(c[2]),$(c[1])}"))
					println(satf, @sprintf "-%d -%d 0" get_number("p(s_$(c[2])=$i)") get_number("p(s_$(c[1])=$j)"))
				end
			end
		end
	end
	close(satf)
end

print_cond()
out_repl()

using Printf

n = 5
m = 3
variables = ["m"]
cond = []

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


max = 50
p = [5,8,4,5,4,6,6,5,5]
# p = [55,30,20,10,62,32,27,30,48]
# p = [661,6,333,  168,489,343,  171,505,324]
p = [4, 1, 9, 9, 4, 8, 2, 8, 6, 1, 7, 5, 4, 9, 6]


function print_cond()
	for v in variables
		for i in 0:max
			print("p($v=$i) ")
		end

		println("")

		for i in 0:max
			for j in (i+1):max
				println("-p($v=$i) -p($v=$j)")
			end
		end
	end

	for i in 1:(n*m)
		for j in 0:max
			if j < p[i]
				println("-p(m=$j)")
			else
				for k in (j-p[i]+1):max
					println("-p(m=$j) -p(s_$i=$k)")
				end
			end
		end
	end

	for c in cond
		println("q_{$(c[1]),$(c[2])} q_{$(c[2]),$(c[1])}")


		for i in 0:max
			if i < p[ c[2] ]
				println("-q_{$(c[1]),$(c[2])} -p(s_$(c[1])=$i)")
			else
				for j in (i-p[c[2]]+1):max
					println("-q_{$(c[1]),$(c[2])} -p(s_$(c[1])=$i) -p(s_$(c[2])=$j)")
				end
			end
		end

		for i in 0:max
			if i < p[ c[1] ]
				println("-q_{$(c[2]),$(c[1])} -p(s_$(c[2])=$i)")
			else
				for j in (i-p[c[1]]+1):max
					println("-q_{$(c[2]),$(c[1])} -p(s_$(c[2])=$i) -p(s_$(c[1])=$j)")
				end
			end
		end
	end
end

print_cond()

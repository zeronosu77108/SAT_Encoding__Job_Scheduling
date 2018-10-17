class Scheduling 
    def initialize
        @n = 3
        @m = 3
        @variables = ["m"]
        @conditions = []

        @numbers = {}
        @num_count = 0
        @tseitin_count = "a"

        @satfile = "scheduling_log.sat"
        @replfile = "scheduling_log.repl"

        @max = 17
        @max_b = Math.log2(@max).ceil

        @p = [5,8,4,5,4,6,6,5,5]
        init_conditions()
    end


    def init_conditions()
        0.upto @n-1  do |i|
            1.upto @n  do |j|
                @variables << "s_#{@m*i+j}"
            end
        end

        0.upto @n-1 do |i|
            1.upto @n do |j|
                (j+1).upto @m do |k|
                    @conditions << [i*@m+j, i*@m+k]
                end
            end
        end

        1.upto @m do |i|
            0.upto @n-1 do |j|
                (j+1).upto(@n-1) do |k|
                    @conditions << [@m*j+i, @m*k+i]
                end
            end
        end
    end


    def get_number(s)
        if @numbers.has_key?(s) == false
            @num_count += 1
            @numbers[s] = @num_count
        end

        return @numbers[s]
    end


    def out_repl
        f = open(@replfile, "w")
        @numbers.sort_by{|_,v| v}.each do |key, value|
            f.puts "#{value} #{key}"
        end
    end



    def print_define_variables(f)
        # define Integer Proposition variables
        @variables.each do |v|
            @max_b.times do |i|
                get_number("#{v}^{(#{i})}")
            end

            (@max+1).upto (2**@max_b-1) do |i|
                @max_b.times do |j|
                    if ((i >> j)&1 == 1)
                        f.print "-#{get_number("#{v}^{(#{j})}")} "
                    end
                end
                f.puts "0"
            end
        end

        # define carry Proposition variables
        @variables.each do |v|
            @max_b.times do |i|
                get_number("c_{#{v}^{(#{i})}}")
            end
            f.puts "-#{get_number("c_{#{v}^{(#{@max_b})}}")} 0"
        end
    end


    def print_max_conditions(f)
        1.upto(@n*@m) do |i|
            f.puts "-#{get_number("s_#{i}^{(#{@max_b-1})}")} -#{get_number("c_{s_#{i}^{(#{@max_b-1})}}")} 0"
            f.puts "#{get_number("m^{(#{@max_b-1})}")} -#{get_number("s_#{i}^{(#{@max_b-1})}")} 0"
            f.puts "#{get_number("m^{(#{@max_b-1})}")} -#{get_number("c_{s_#{i}^{(#{@max_b-1})}}")} 0"

            (@max_b-2).downto 0 do |j|
                f.puts "#{get_number(@tseitin_count)} #{get_number(@tseitin_count.next)} 0"

                lambda {
                    t = get_number(@tseitin_count)
                    s = get_number("s_#{i}^{(#{j+1})}")
                    c1 = get_number("c_{s_#{i}^{(#{j+1})}}")
                    m = get_number("m^{(#{j+1})}")
                    c2 = get_number("c_{s_#{i}^{(#{j+2})}}")

                    if (@p[i-1] >> (j+1))&1 == 1
                        f.puts "-#{t} #{c2} 0"
                        f.puts "-#{t} -#{c1} #{m} -#{c2} 0"
                        f.puts "-#{t} -#{s} #{m} -#{c2} 0"
                        f.puts "-#{t} -#{s} -#{c2} 0"
                    else
                        f.puts "-#{t} #{m} #{c2} 0"
                        f.puts "-#{t} -#{c1} -#{m} #{c2} 0"
                        f.puts "-#{t} -#{s} -#{m} #{c2} 0"
                        f.puts "-#{t} -#{s} -#{c1} #{m} 0"
                    end
                }.call

                lambda {
                    t = get_number(@tseitin_count.next)
                    s = get_number("s_#{i}^{(#{j})}")
                    c1 = get_number("c_{s_#{i}^{(#{j})}}")
                    m = get_number("m^{(#{j})}")
                    c2 = get_number("c_{s_#{i}^{(#{j+1})}}")
                    
                    if (@p[i-1] >> j)&1 == 1
                        f.puts "-#{t} #{m} #{c2} 0"
                        f.puts "-#{t} -#{c1} -#{m} #{c2} 0"
                        f.puts "-#{t} -#{s} -#{m} #{c2} 0"
                        f.puts "-#{t} -#{s} -#{c1} #{m} 0"
                        f.puts "-#{s} #{c2} 0"
                        f.puts "-#{c1} #{c2} 0"
                    else
                        f.puts "-#{t} -#{s} -#{c1} #{c2} 0"
                        f.puts "-#{t} -#{s} #{m} #{c2} 0"
                        f.puts "-#{t} -#{c1} #{m} #{c2} 0"
                        f.puts "-#{s} -#{c1} #{c2} 0"
                    end
                }.call

                @tseitin_count.next!.next!
            end
        end
    end


    def print_exclusive_conditions(f)
    end


    def print_conditions
        f = open(@satfile, "w")
        print_define_variables(f)
        print_max_conditions(f)
        print_exclusive_conditions(f)
        f.close
    end



    def main()
        print_conditions
        out_repl
    end
end

s = Scheduling.new()
s.main()

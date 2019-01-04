class Scheduling # {{{
  def initialize# {{{
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
    @max_b = (Math.log2(@max)+1).floor

    @p = [5,8,4,5,4,6,6,5,5]
    p @p
    init_conditions()
    p @conditions
  end# }}}

  def init_conditions()# {{{
    0.upto @n-1  do |i|
      1.upto @m  do |j|
        @variables << "s_#{@m*i+j}"
      end
    end

    0.upto @m-1 do |i|
      1.upto @n-1 do |j|
        (j+1).upto @n do |k|
          @conditions << [i*@n+j, i*@n+k]
        end
      end
    end

    1.upto @n do |i|
      0.upto @m do |j|
        (j+1).upto @m-1 do |k|
          @conditions << [@n*j+i, @n*k+i]
        end
      end
    end
  end# }}}

  def get_number(s)# {{{
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
  end# }}}

  def print_define_variables(f)# {{{
    # define Integer Proposition variables
    @variables.each_with_index do |v,vi|
      @max_b.times do |i|
        get_number("#{v}^{(#{i})}")
      end

      start_tmp = @max + 1
      start_tmp -= @p[vi-1] if vi>0
      puts start_tmp

      start_tmp.upto (2**@max_b-1) do |i|
        @max_b.times do |j|
          if ((i >> j)&1 == 1)
            t = get_number("#{v}^{(#{j})}")
            f.print "-#{t} "
          end
        end
        f.puts "0"
      end

    end


    # define carry Proposition variables
    1.upto(@n*@m) do |i|
      0.upto @max_b do |j|
        c2 = get_number("c_{s_#{i}^{(#{j})}}")
        f.puts "-#{c2} 0" if j==0
        if j > 0
          s1  = get_number("s_#{i}^{(#{j-1})}")
          c1 = get_number("c_{s_#{i}^{(#{j-1})}}")

          if (@p[i-1] >> j-1)&1 == 1
            f.puts "-#{s1} #{c2} 0"
            f.puts "-#{c1} #{c2} 0"
            f.puts "-#{c2} #{s1} #{c1} 0"
          else
            f.puts "-#{s1} -#{c1} #{c2} 0"
            f.puts "-#{c2} #{s1} 0"
            f.puts "-#{c2} #{c1} 0"
          end
        end
      end
    end
  end# }}}

  def print_leq_condition(f, flag, t, s1, c1, s2, c2, ff=false)# {{{
    case flag
    when -1
      f.puts "-#{t} #{s1} #{c1} #{s2} #{c2} 0"
      f.puts "-#{t} #{s1} -#{c1} #{s2} #{c2} 0"
      f.puts "-#{t} #{s1} -#{c1} -#{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} #{c1} #{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} #{c1} -#{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} -#{c1} #{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} -#{c1} #{s2} -#{c2} 0"
      f.puts "-#{t} -#{s1} -#{c1} -#{s2} #{c2} 0"

    when 0
      f.puts "-#{t} #{s1} -#{c1} #{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} #{c1} #{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} -#{c1} #{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} -#{c1} -#{s2} #{c2} 0"

    when 1
      f.puts "-#{t} #{s1} #{c1} #{s2} #{c2} 0"
      f.puts "-#{t} #{s1} -#{c1} #{s2} #{c2} 0"
      f.puts "-#{t} #{s1} -#{c1} -#{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} #{c1} #{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} #{c1} -#{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} -#{c1} #{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} -#{c1} #{s2} -#{c2} 0"
      f.puts "-#{t} -#{s1} -#{c1} -#{s2} #{c2} 0"

    when 2
      f.puts "-#{t} #{s1} #{c1} #{s2} #{c2} 0"
      f.puts "-#{t} #{s1} #{c1} -#{s2} #{c2} 0"
      f.puts "-#{t} #{s1} -#{c1} #{s2} #{c2} 0"
      f.puts "-#{t} #{s1} -#{c1} #{s2} -#{c2} 0"
      f.puts "-#{t} #{s1} -#{c1} -#{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} #{c1} #{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} #{c1} #{s2} -#{c2} 0"
      f.puts "-#{t} -#{s1} #{c1} -#{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} -#{c1} #{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} -#{c1} #{s2} -#{c2} 0"
      f.puts "-#{t} -#{s1} -#{c1} -#{s2} #{c2} 0"
      f.puts "-#{t} -#{s1} -#{c1} -#{s2} -#{c2} 0"

    end
  end# }}}

  def print_max_conditions(f)# {{{
    1.upto(@n*@m) do |i|
      f.puts "-#{get_number("s_#{i}^{(#{@max_b-1})}")} -#{get_number("c_{s_#{i}^{(#{@max_b-1})}}")} 0"
      f.puts "#{get_number("m^{(#{@max_b-1})}")} -#{get_number("s_#{i}^{(#{@max_b-1})}")} 0"
      f.puts "#{get_number("m^{(#{@max_b-1})}")} -#{get_number("c_{s_#{i}^{(#{@max_b-1})}}")} 0"

      (@max_b-2).downto 0 do |j|
        f.puts "#{get_number(@tseitin_count)} #{get_number(@tseitin_count.next)} 0"

        lambda {# {{{
          t = get_number(@tseitin_count)
          s = get_number("s_#{i}^{(#{j+1})}")
          c1 = get_number("c_{s_#{i}^{(#{j+1})}}")
          m = get_number("m^{(#{j+1})}")
          c2 = get_number("c_{s_#{i}^{(#{j+2})}}")

          if (@p[i-1] >> (j+1))&1 == 1
            print_leq_condition(f, 2, t, s, c1, m, c2)
          else
            print_leq_condition(f, -1, t, s, c1, m, c2)
          end
        }.call# }}}

        lambda {# {{{
          t = get_number(@tseitin_count.next)
          s = get_number("s_#{i}^{(#{j})}")
          c1 = get_number("c_{s_#{i}^{(#{j})}}")
          m = get_number("m^{(#{j})}")
          c2 = get_number("c_{s_#{i}^{(#{j+1})}}")

          if (@p[i-1] >> j)&1 == 1
            print_leq_condition(f, 1, t, s, c1, m, c2)
          else
            print_leq_condition(f, 0, t, s, c1, m, c2)
          end
        }.call# }}}

        @tseitin_count.next!.next!
      end
    end
  end# }}}

  def print_exclusive_conditions(f)# {{{
    @conditions.each do |cond|
      tseitin_variable = []
      tseitin_variable << get_number(@tseitin_count)
      tseitin_variable << get_number(@tseitin_count.next!)
      f.puts "#{tseitin_variable[0]} #{tseitin_variable[1]} 0"

      @tseitin_count.next!

      tseitin_variable.each do |tv|
        puts "s_#{cond[0]} + #{@p[cond[0]-1]} <= s_#{cond[1]}"
        f.puts "-#{tv} -#{get_number("s_#{cond[0]}^{(#{@max_b-1})}")} -#{get_number("c_{s_#{cond[0]}^{(#{@max_b-1})}}")} 0"
        f.puts "-#{tv} #{get_number("s_#{cond[1]}^{(#{@max_b-1})}")} -#{get_number("s_#{cond[0]}^{(#{@max_b-1})}")} 0"
        f.puts "-#{tv} #{get_number("s_#{cond[1]}^{(#{@max_b-1})}")} -#{get_number("c_{s_#{cond[0]}^{(#{@max_b-1})}}")} 0"

        prev_tv = ""

        (@max_b-2).downto 0 do |i|
          f.puts "-#{prev_tv} " if prev_tv != ""
          
          f.puts "-#{tv} #{get_number(@tseitin_count)} #{get_number(@tseitin_count.next)} 0"
          lambda {
            t  = get_number(@tseitin_count)
            s1 = get_number("s_#{cond[0]}^{(#{i+1})}")
            c1 = get_number("c_{s_#{cond[0]}^{(#{i+1})}}")
            s2 = get_number("s_#{cond[1]}^{(#{i+1})}")
            c2 = get_number("c_{s_#{cond[0]}^{(#{i+2})}}")
            if (@p[cond[0]-1] >> (i+1))&1 == 1
              print_leq_condition(f, 2, t, s1, c1, s2, c2, tv)
            else
              print_leq_condition(f, -1, t, s1, c1, s2, c2, tv)
            end
          }.call

          lambda {
            t  = get_number(@tseitin_count.next)
            s1 = get_number("s_#{cond[0]}^{(#{i})}")
            c1 = get_number("c_{s_#{cond[0]}^{(#{i})}}")
            s2 = get_number("s_#{cond[1]}^{(#{i})}")
            c2 = get_number("c_{s_#{cond[0]}^{(#{i+1})}}")
            print "#{(@p[cond[0]-1] >> i)&1} "
            if (@p[cond[0]-1] >> i)&1 == 1
              print_leq_condition(f, 1, t, s1, c1, s2, c2, tv)
            else
              print_leq_condition(f, 0, t, s1, c1, s2, c2, tv)
            end
            prev_tv = t
          }.call
          @tseitin_count.next!.next!

          
        end
        cond = cond[1], cond[0]
        puts ""
        puts ""
      end
    end
  end# }}}

  def print_conditions# {{{
    f = open(@satfile, "w")
    print_define_variables(f)
    # print_max_conditions(f)
    print_exclusive_conditions(f)
    f.close
  end# }}}

  def main()# {{{
    print_conditions
    out_repl
  end# }}}
end# }}}

s = Scheduling.new()
s.main()

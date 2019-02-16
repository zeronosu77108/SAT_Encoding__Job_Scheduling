class Scheduling # {{{
  def initialize# {{{
    @n = 2
    @m = 2
    @B = 4
    @variables = ["m"]
    @conditions = []

    @numbers = {}
    @num_count = 0
    @tseitin_count = "a"

    @satfile = "scheduling_compact-order.sat"
    @replfile = "scheduling_compact-order.repl"

    @max = 17
    @max_b = @max.to_s(@B).chars.length
    puts "digit : #{@max_b}"
        
    # (Math.log2(@max)+1).floor

    @p = [5,8,4,5,4,6,6,5,5]
    # p @p
    init_conditions()
    print "conditions : "
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
      (@max_b).times do |i|
          prev = 0
          (@B-1).times do |j|
              current = get_number("p(#{v}^{(#{i})}<=#{j})")
              f.puts "-#{prev} #{current} 0" if prev != 0
              prev = current
          end
      end
    end

    # define Domain
    1.upto (@n*@m) do |vi|
      # max - pi をしてその値を B進 に分解
      # si の各桁が その値以下であるという制約を追加す:
      (@max - @p[vi-1]).to_s(@B).rjust(@max_b, '0').chars.map(&:to_i).reverse.each_with_index do |m,i|
          next if m >= @B-1
          v = get_number("p(s_#{vi}^{(#{i})}<=#{m})")
          f.print "#{prev}" if prev != ""
          f.puts "#{v} 0"
          prev += "-#{v} " if m != 0
          p prev
        end
    end



    # define carry Proposition variables
    1.upto(@n*@m) do |i|
      p = @p[i-1].to_s(@B).chars.map(&:to_i)
      # p @p[i-1]
      p p
      0.upto (@max_b-1) do |j|
        c2 = get_number("c_{s_#{i}^{(#{j})}}")

        # c_0 は必ず 0 になる
        f.puts "-#{c2} 0" if j==0

        # 2回目以降
        if j > 0
          puts "p[j-1] : #{p[j-1]}"

          # c_i が 0 の場合
          # ¬p(s1 <= (B-p1-1)) -> c2
          # p1 が 0 のときはスキップ（桁上げが起きない）
          s1 = get_number("p(s_#{i}^{(#{j-1})}<=#{(@B-p[j-1]-1)})")
          if p[j-1] != 0
            f.puts "#{s1} #{c2} 0"
          end

          # c2 -> ¬p(s1 <= (B-p1-1)) ∨ q
          tseitin = get_number(@tseitin_count); @tseitin_count.next!
          f.puts "-#{c2} -#{s1} #{tseitin} 0"

          # c_i が 1 の場合
          # ( ¬p(s1 <= (B-p1-2)) ∧ c1 ) -> c2
          s1 = get_number("p(s_#{i}^{(#{j-1})}<=#{(@B-p[j-1]-2)})")
          c1 = get_number("c_{s_#{i}^{(#{j-1})}}")
          f.puts "-#{c1} #{s1} #{c2} 0"

          # q  -> ¬p(s1 <= (B-p1-2))
          # q  -> c1
          f.puts "-#{tseitin} -#{s1} 0"
          f.puts "-#{tseitin} #{c1} 0"
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
        # puts "s_#{cond[0]} + #{@p[cond[0]-1]} <= s_#{cond[1]}"
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
            # print "#{(@p[cond[0]-1] >> i)&1} "
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
        # puts ""
        # puts ""
      end
    end
  end# }}}

  def print_conditions# {{{
    f = open(@satfile, "w")
    print_define_variables(f)
    # print_max_conditions(f)
    # print_exclusive_conditions(f)
    f.close
  end# }}}

  def main()# {{{
    print_conditions
    out_repl
  end# }}}
end# }}}

s = Scheduling.new()
s.main()

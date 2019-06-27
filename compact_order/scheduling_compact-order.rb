class Scheduling # {{{
  def initialize# {{{
    input_file = ""
    if ARGV.length <= 0
      puts "OSS file : "
      input_file = gets
    else
      input_file = ARGV[0]
    end

    s = []
    File.open(input_file, 'r') do |f|
      f.each_line do |line|
          next if line.match(/^#/)
          s << line.chomp.split.map(&:to_i)
      end
    end
    @n,@m,@max,@B = s.shift
    @p = s.flatten
    # p @p
      
    # @n = 3
    # @m = 3
    # @B = 4
    @variables = ["m"]
    @conditions = []
    
    @numbers = {}
    @num_count = 0
    @tseitin_count = "a"
    
    @satfile = "scheduling_compact-order.sat"
    @replfile = "scheduling_compact-order.repl"

    # @max = 17000
    @max_b = @max.to_s(@B).chars.length
    puts "n=#{@n}  m=#{@m}  max=#{@max}"
    puts "B=#{@B}  digit: #{@max_b}"
    puts ""

    puts "process times"
    1.upto(@n*@m) do |i|
      print "#{@p[i-1]} "
      puts "" if i % @n==0
    end
    puts ""
    
    # @p =
    print "conditions : "
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
      (@max_b).times do |i|
          prev = 0
          (@B-1).times do |j|
              current = get_number("p(#{v}^{(#{i})}<=#{j})")
              f.puts "-#{prev} #{current} 0" if prev != 0
              prev = current
              
              # f.puts "#{current} 0" if j<=0 && i>=@max_b
          end
      end
    end

    # define Domain
    1.upto (@n*@m) do |vi|# {{{
      prev = ""
      # max - pi をしてその値を B進 に分解
      # si の各桁が その値以下であるという制約を追加す:
      # puts "max : #{@max - @p[vi-1]}"
      max = (@max - @p[vi-1]).to_s(@B).rjust(@max_b, '0').chars.map(&:to_i)
      # print "define Domain max : "
      # p max
      max.each_with_index do |m,i|
          next if m > @B-1
          if m == @B-1 && m-1>=0
            v = get_number("p(s_#{vi}^{(#{@max_b-i-1})}<=#{m-1})") 
            prev += "#{v} " #if m != 0
            next
          end
          v = get_number("p(s_#{vi}^{(#{@max_b-i-1})}<=#{m})")

          f.print "#{prev}" if prev != ""
          f.puts "#{v} 0"
          if m != 0 && m-1>=0
            v = get_number("p(s_#{vi}^{(#{@max_b-i-1})}<=#{m-1})")
            prev += "#{v} "
          end
          # p prev
        end
    end# }}}



    # define carry Proposition variables
    1.upto(@n*@m) do |i|# {{{
      0.upto (@max_b) do |j|
        get_number("c_{s_#{i}^{(#{j})}}")
      end
    end# }}}

    1.upto(@n*@m) do |i|# {{{
      p = @p[i-1].to_s(@B).rjust(@max_b, '0').chars.map(&:to_i)
      # p @p[i-1]
      # p p
      0.upto (@max_b-1) do |j|
        c2 = get_number("c_{s_#{i}^{(#{j})}}")

        # c_0 は必ず 0 になる
        f.puts "-#{c2} 0" if j==0

        # 2回目以降
        if j > 0
          # puts "p[#{j-1}] : #{p[j-1]}"

          # c_i が 0 の場合
          # ¬p(s1 <= (B-p1-1)) -> c2
          s1 = 0
          if (@B-p[j-1]-1 < @B-1) && (@B-p[j-1]-1 >= 0) 
            s1 = get_number("p(s_#{i}^{(#{j-1})}<=#{(@B-p[j-1]-1)})")
            f.puts "#{s1} #{c2} 0"
          end

          # c2 -> ¬p(s1 <= (B-p1-1)) ∨ q
          tseitin = get_number(@tseitin_count); @tseitin_count.next!
          if  (@B-p[j-1]-2 < @B-1) && (@B-p[j-1]-2 >= 0)
            tmp = @B - p[j-1] - 2
            tmp = 0 if tmp<0
            s1 = get_number("p(s_#{i}^{(#{j-1})}<=#{tmp})") 
          end
          f.print "-#{c2} " if (@B-p[j-1]-1 < @B-1) && (@B-p[j-1]-1 >= 0) || (@B-p[j-1]-2 < @B-1) && (@B-p[j-1]-2 >= 0)
          f.print "-#{s1} " if (@B-p[j-1]-1 < @B-1) && (@B-p[j-1]-1 >= 0) 
          f.print "#{tseitin} " if (@B-p[j-1]-2 < @B) && (@B-p[j-1]-2 >= 0)
          f.puts "0"

          # c_i が 1 の場合
          # ( ¬p(s1 <= (B-p1-2)) ∧ c1 ) -> c2
          if (@B-p[j-1]-2 < @B) && (@B-p[j-1]-2 >= 0) 
            if (@B-p[j-1]-2 == 3 )
              c1 = get_number("c_{s_#{i}^{(#{j-1})}}")
              f.puts "-#{c1} #{c2} 0"
              f.puts "-#{tseitin} #{c1} 0"
            else
              s1 = get_number("p(s_#{i}^{(#{j-1})}<=#{(@B-p[j-1]-2)})")
              c1 = get_number("c_{s_#{i}^{(#{j-1})}}")
              f.puts "-#{c1} #{s1} #{c2} 0"
            f.puts "-#{tseitin} -#{s1} 0"
            end

            # q  -> ¬p(s1 <= (B-p1-2))
            # q  -> c1
            # f.puts "-#{tseitin} #{c1} 0"
          end
        end
      end
      # 最上位桁は必ず偽となる
      f.puts "-#{get_number("c_{s_#{i}^{(#{@max_b})}}")} 0"
      # f.puts "-#{get_number("c_{s_#{i}^{(#{@B-1})}}")} 0"
    end# }}}
  end# }}}

  def print_leq_condition(f, t, s1, c1, s2, c2, p, ff=false)# {{{
    # puts "#{s2} + #{p} + #{c1} <= #{s1} + #{@B}#{c2}"
    # t  = get_number(@tseitin_count)
    # s1 = "s_#{cond[0]}^{(#{i+1})}"
    # c1 = "c_{s_#{cond[0]}^{(#{i+1})}}"
    # s2 = "s_#{cond[1]}^{(#{i+1})}"
    # c2 = "c_{s_#{cond[0]}^{(#{i+2})}}"
    # p  =@p[cond[0]-1]

    (@B).times do |i|
      vs = [ i+@B-p-1, i+@B-p, i-p-1, i-p ]
      vs_str = [ "i+@B-p-1", "i+@B-p", "i-p-1", "i-p" ]
      # puts "2019/05/08 : #{s1}"
      s1_t = get_number "p(#{s1}<=#{i})" if i < @B-1
      # puts "p(#{s1}<=#{i})"
      c1_t = -1 * (get_number c1)
      c2_t = -1 * (get_number c2)

      vs.each_with_index do |v, vi|
        # puts "v#{vi} #{vs_str[vi]} : #{v}"
        if v < @B-1
          f.print "-#{t} "
          f.print "-#{s1_t} " if i < @B-1
          f.print "#{c1_t} #{c2_t} "
          if v >= 0
            s2_t = get_number "p(#{s2}<=#{v})"
            # puts "p(#{s2}<=#{v})"
            f.print "#{s2_t} "
          else 
            # puts "禁止"
          end
          f.puts "0"
        end
        c1_t *= -1
        if c1_t < 0
          c2_t *= -1
        end
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

      # a ∨ b
      # a -> (s1 + p1 <= s2)
      # b -> (s2 + p2 <= s1)
      tseitin_variable.each do |tv|
        p_l = @p[cond[1]-1].to_s(@B).rjust(@max_b, '0').chars.map(&:to_i)
        
        # puts "s_#{cond[1]} + #{p_l} <= s_#{cond[0]}"

        # p = p[cond[0]-1]

        # 1 桁目
        # s1 + p1 + c2 <= m + 4c3
        p = p_l[0]
        # puts "p : #{p}"
        (@B).times do |i|
          vs = [ i+@B-p-1, i+@B-p, i-p-1, i-p ]
          vs_str = [ "i+@B-p-1", "i+@B-p", "i-p-1", "i-p" ]
           
          s1 = get_number "p(s_#{cond[0]}^{(#{@max_b-1})}<=#{i})" if i < @B-1
          # puts "p(s_#{cond[0]}^{(#{@max_b-1})}<=#{i})"
          c1 = -1 * (get_number "c_{s_#{cond[1]}^{(#{@max_b-1})}}")
          c2 = -1 * (get_number "c_{s_#{cond[1]}^{(#{@max_b})}}")

          vs.each_with_index do |v, vi|
            # puts "v#{vi} #{vs_str[vi]} : #{v}"
            if v < @B-1
              f.print "-#{tv} "
              f.print "-#{s1} " if i < @B-1
              f.print "#{c1} #{c2} "
              # f.print "-#{tv} -#{s1} #{c1} #{c2} "
              if v >= 0
                s2 = get_number "p(s_#{cond[1]}^{(#{@max_b-1})}<=#{v})"
                # puts "p(s_#{cond[1]}^{(#{@max_b-1})}<=#{v})"
                f.print "#{s2} "
              else 
                # puts "禁止"
              end
              f.puts "0"
            end
            c1 *= -1
            if c1 < 0
              c2 *= -1
            end
          end
        end

        # 2 桁目以降
        # puts "#####"
        # puts "2桁目以降"
        prev_tv = ""
        p_l.reverse!
        (@max_b-2).downto 0 do |i|
          f.print "-#{prev_tv} " if prev_tv != ""
          
          f.puts "-#{tv} #{get_number(@tseitin_count)} #{get_number(@tseitin_count.next)} 0"
          lambda {
            t  = get_number(@tseitin_count)
            s1 = "s_#{cond[1]}^{(#{i+1})}"
            c1 = "c_{s_#{cond[1]}^{(#{i+1})}}"
            s2 = "s_#{cond[0]}^{(#{i+1})}"
            c2 = "c_{s_#{cond[1]}^{(#{i+2})}}"
            # p  = @p[cond[0]-1]
            p = p_l[i+1]
            
            print_leq_condition(f, t, s2, c1, s1, c2, p+1, tv)
          }.call
          
          lambda {
            t  = get_number(@tseitin_count.next)
            s1 = "s_#{cond[1]}^{(#{i+0})}"
            c1 = "c_{s_#{cond[1]}^{(#{i+0})}}"
            s2 = "s_#{cond[0]}^{(#{i+0})}"
            c2 = "c_{s_#{cond[1]}^{(#{i+1})}}"
            # p  = @p[cond[0]-1]
            p = p_l[i]
            
            print_leq_condition(f, t, s2, c1, s1, c2, p, tv)
            
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

    # f.puts "print_define_variables(f)"
    print_define_variables(f)
    
    # f.puts "print_exclusive_conditions(f)"
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

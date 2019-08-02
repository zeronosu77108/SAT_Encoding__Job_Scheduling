class Scheduling # {{{
  def initialize# {{{
    @debug_flag = true
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
    print "conditions : " if @debug_flag
    init_conditions()
    p @conditions if @debug_flag
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
    @variables.each_with_index do |v|
      (@max_b).times do |i|
          (@B-1).times do |j|
            get_number("p(#{v}^{(#{i})}<=#{j})")
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
      p max
      perv = ""
      prev_str = ""
      max.each_with_index do |m,i|
        (m+1).upto(@B-1) do |j|
          v = get_number("p(s_#{vi}^{(#{@max_b-i-1})}=#{j})")
          puts "#{prev_str} ¬p(s_#{vi}^{(#{@max_b-i-1})}=#{j})" if @debug_flag
          f.puts "#{prev} #{-1 * v} 0"
        end
        prev += " #{-1*get_number("p(s_#{vi}^{(#{@max_b-i-1})}=#{m})")}"
        prev_str += " #{("p(s_#{vi}^{(#{@max_b-i-1})}=#{m})")} →"
      end
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
        p_l = @p[cond[0]-1].to_s(@B).rjust(@max_b, '0').chars.map(&:to_i)
        p p_l if @debug_flag
        
        prev_tv = ""
        puts "#{tseitin_variable[0]} #{tseitin_variable[1]} 0" if @debug_flag
        prev_tv = 0
        current_tv = 0
        p_l.each_with_index do |pi,p_index|
          s = pi - 1
          s=0 if s<0

          s.upto(@B-1) do |i|# {{{
            wff = "-#{tv} "
            wff_str = "-#{tv} "
            wff += "#{prev_tv} " if prev_tv !=0
            wff_str += "#{prev_tv} " if prev_tv!=0
            print_flag = false

            if i-pi >= 0 && i-pi<@B-1
              s1 = get_number("p(s_#{cond[0]}^{(#{@max_b-1-p_index})}<=#{i-pi})")
              s1_str = ("p(s_#{cond[0]}^{(#{@max_b-1-p_index})}<=#{i-pi})")
              wff += "#{s1} "
              wff_str += "#{s1_str} "
              print_flag = true
            end

            if i < 3 
              s2 = -1 * get_number("p(s_#{cond[1]}^{(#{@max_b-1-p_index})}<=#{i})")
              s2_str = ("-p(s_#{cond[1]}^{(#{@max_b-1-p_index})}<=#{i})")
              wff += "#{s2} "
              wff_str += "#{s2_str} "
              print_flag = true
            end
            
            f.puts "#{wff}0" if print_flag 
            puts wff_str if @debug_flag && print_flag
          end# }}}


          pi.upto(@B-1) do |i|# {{{{{{
            wff = "-#{tv} "
            wff_str = "-#{tv} "
            wff += "#{prev_tv} " if prev_tv != 0
            wff_str += "#{prev_tv} " if prev_tv !=0
            print_flag = false

            if i-pi-1 >= 0 && i-pi-1<@B-1
              s1 = get_number("p(s_#{cond[0]}^{(#{@max_b-1-p_index})}<=#{i-pi-1})")
              s1_str = ("p(s_#{cond[0]}^{(#{@max_b-1-p_index})}<=#{i-pi-1})")
              wff += "#{s1} "
              wff_str += "#{s1_str} "
              print_flag = true
            end

            if i < @B-1
              s2 = -1 * get_number("p(s_#{cond[1]}^{(#{@max_b-1-p_index})}<=#{i})")
              s2_str = ("-p(s_#{cond[1]}^{(#{@max_b-1-p_index})}<=#{i})")
              wff += "#{s2} "
              wff_str += "#{s2_str} "
              print_flag = true
            end

            current_tv = get_number(@tseitin_count)
            wff += "#{current_tv} "
            wff_str += "#{current_tv} "

            f.puts "#{wff}0" if print_flag
            puts wff_str if @debug_flag && print_flag
          end# }}}}}}

          # wff = "-#{tv} "
          # wff_str = "-#{tv} "
          # wff += "#{prev_tv} " if prev_tv != 0
          # wff_str += "#{prev_tv} " if prev_tv !=0
          #
          # wff += "#{current_tv} " if pi==3
          # wff_str += "#{current_tv} " if pi==3

          f.puts "#{wff}0" if pi == 3
          puts "#{wff_str}0" if pi == 3 && @debug_flag
          
          prev_tv = -1 * current_tv
          @tseitin_count.next!
        end

        cond = cond[1], cond[0]
        puts "" if @debug_flag
      end
    end
  end# }}}
  
  def print_conditions# {{{
    f = open(@satfile, "w")
    print_define_variables(f)
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

using Test, Chevie

function labelled_springer_character(u,h,name,local_label)
  c=only(findall(x->x.name==name,u.classes))
  a=only(findall(==(local_label),charinfo(u.classes[c].Au).charparams))
  i,j=only([(i,j) for (i,s) in enumerate(u.springerseries)
                  for (j,pair) in enumerate(s[:locsys]) if pair==[c,a]])
  s=u.springerseries[i]
  hc=i==1 ? 1 : s[:hc]
  k=charnumbers(h.harishChandra[hc])[j]
  (s[:levi],only(h.charParams[k]),only(h.charSymbols[k]))
end

@testset "Labels in the Springer/Harish-Chandra correspondence" begin
  @testset "Classical cuspidal data and bipartitions" begin
    # Lusztig–Spaltenstein symbols (rho,s)=(4,2) and (4,0): see
    # Geck–Malle (2000), §§2.7, 2.17, DOI 10.1090/S0002-9947-99-02210-2.
    # Shoji, arXiv:0712.2296, Theorem 6.2 and Corollary 6.3 identify
    # the corresponding almost characters. Pin the labels, not array indices.
    fixtures=((:B,3,2,"411",[[1,1]],"B_2",[1,1],[[0,1,2,3],[1]]),
      (:B,3,2,"6",[[1,1]],"B_2",[2],[[0,1,3],Int[]]),
      (:C,4,2,"62",[[1,1]],"B_2",[[1,1],Int[]],[[0,2,3],Int[]]),
      (:C,4,2,"611",[[1,1]],"B_2",[[1],[1]],[[0,1,2,4],[1]]),
      (:C,4,2,"41111",[[1,1]],"B_2",[Int[],[1,1]],[[0,1,2,3,4],[1,2]]),
      (:C,4,2,"8",[[1,1]],"B_2",[[2],Int[]],[[0,1,4],Int[]]),
      (:C,4,2,"4(22)",[[1,1]],"B_2",[Int[],[2]],[[0,1,2,3],[2]]),
      (:B,6,6,"84",[[1,1],[2]],"B_6",[Int[],Int[]],[[0,1,2,3,4],Int[]]),
      (:D,4,4,"62",[[1,1]],"D_4",[Int[],Int[]],[[0,1,2,3],Int[]]),
      (:D,5,4,"6211",[[1,1]],"D_4",[1,1],[[0,1,2,3,4],[1]]),
      (:D,5,4,"82",[[1,1]],"D_4",[2],[[0,1,2,4],Int[]]))
    for (s,n,r,name,local_label,cuspidal,relative,symbol) in fixtures
      w=coxgroup(s,n)
      u,h=UnipotentClasses(w,2),UnipotentCharacters(w)
      levi,label,S=labelled_springer_character(u,h,name,local_label)
      @test levi==collect(1:r)
      @test label==(cuspidal=>relative)
      @test S==CharSymbol(symbol)
    end
  end

  @testset "Degenerate type D labels" begin
    # Both copies of a degenerate symbol must remain distinguished. The
    # package's + convention changes between ranks 0 and 2 modulo 4.
    for (n,name,part,plus) in ((4,"(2222)",[1,1],1),(4,"(44)",[2],1),
                             (6,"(222222)",[1,1,1],0),(6,"(44)(22)",[2,1],0),
                             (6,"(66)",[3],0))
      w=coxgroup(:D,n)
      u,h=UnipotentClasses(w,2),UnipotentCharacters(w)
      for (suffix,tag) in (("+",plus),("-",1-plus))
        levi,label,S=labelled_springer_character(u,h,name*suffix,Any[])
        @test isempty(levi)
        @test label==(""=>[part,part,2,tag])
        @test S==Symbol_partition_tuple([part,part,2,tag],0)
      end
    end
  end

  @testset "E7-induced labelled almost-character values" begin
    # Hetz, arXiv:2309.09915v2, §3.7, §6.2(a), Proposition 3.10.
    # The E7 cuspidal datum is retained on induction. Calibrate the +/-i
    # convention against the existing E7 table; the relative A1 sign has
    # support E7, whereas its trivial character has support E8.
    w7,w8=coxgroup(:E,7),coxgroup(:E,8)
    u7,u8=UnipotentClasses(w7,2),UnipotentClasses(w8,2)
    h7,h8=UnipotentCharacters(w7),UnipotentCharacters(w8)
    for q in (2,4)
      t7,t8=map(u->UnipotentValues(u;q,classes=true),(u7,u8))
      R7,R8=fourier(h7)*t7.scalar,fourier(h8)*t8.scalar
      c7=only(findall(c->c.name=="E_7",u7.classes))
      cols7=findall(x->x[1]==c7,t7.classes)
      for (name,z) in (("E_7[-i]",E(4)),("E_7[i]",-E(4)))
        row7=only(findall(p->first(only(p))==name,h7.charParams))
        base=R7[row7,cols7]
        @test base==big(q)^3*root(big(q))*[1,z,-1,-z]
        for (support,relative) in (("E_7",[1,1]),("E_8",[2]))
          row8=only(findall(==([name=>relative]),h8.charParams))
          c8=only(findall(c->c.name==support,u8.classes))
          cols8=findall(x->x[1]==c8,t8.classes)
          @test R8[row8,cols8]==big(q)^u8.classes[c8].dimBu*base
          if support=="E_7"
            regular=findall(x->u8.classes[x[1]].name=="E_8",t8.classes)
            @test all(iszero,R8[row8,regular])
          end
        end
      end
    end
  end
end

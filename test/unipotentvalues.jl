using Test, Chevie

@testset "Unipotent values in exceptional characteristics" begin
  @testset "Classical Springer series in characteristic two" begin
    # Shoji, arXiv:0712.2296, Theorem 6.2 and Corollary 6.3.
    # The cuspidal ranks in §3.1 are d(d+1) for B/C and 4d² for split D.
    for (s,n) in ((:B,3),(:C,4),(:B,6),(:C,6),(:D,4),(:D,5),(:D,8))
      w=coxgroup(s,n)
      u=UnipotentClasses(w,2)
      h=UnipotentCharacters(w).harishChandra
      @test length(u.springerseries)==length(h)
      for (i,ss) in enumerate(u.springerseries)
        @test get(ss,:hc,i==1 ? 1 : 0)==i
        @test length(ss[:levi])==length(h[i][:levi])
        @test length(ss[:locsys])==length(charnumbers(h[i]))
      end
    end
  end

  @testset "Type A component groups" begin
    # Shoji, arXiv:math/0507057, §3.2: |A(u)| is the prime-to-p part
    # of gcd(lambda); the same restriction applies to the cuspidal pairs.
    for (n,p,d) in ((2,2,1),(3,3,1),(4,2,1),(5,5,1),(6,2,3),(6,3,2))
      u=UnipotentClasses(rootdatum(:sl,n),p)
      @test length(only(c for c in u.classes if c.dimBu==0).Au)==d
      @test all(c->length(c.Au)%p!=0,u.classes)
      @test sum(ss->length(ss[:locsys]),u.springerseries)==
            sum(c->nconjugacy_classes(c.Au),u.classes)
    end
    for (n,p) in ((2,2),(3,3),(4,2),(5,5))
      sl=UnipotentValues(UnipotentClasses(rootdatum(:sl,n),p);q=big(p),classes=true)
      gl=UnipotentValues(UnipotentClasses(rootdatum(:gl,n),p);q=big(p),classes=true)
      @test sl.classes==gl.classes
      @test sl.scalar==gl.scalar
      @test sl.cardClass==gl.cardClass
    end
    @test_throws ErrorException UnipotentValues(UnipotentClasses(rootdatum(:sl,6),2);q=2)
  end

  @testset "Sp4(2) is S6" begin
    u=UnipotentClasses(coxgroup(:B,2),2)
    t=UnipotentValues(u;q=2,classes=true)
    s=coxgroup(:A,5)
    partitions=first.(charinfo(s).charparams)
    cycles=first.(classinfo(s).classparams)
    cycle_by_class=Dict(("1111",1)=>ones(Int,6),("22",1)=>[2,2,1,1],
      ("(22)",1)=>[2,2,2],("211",1)=>[2,1,1,1,1],
      ("4",1)=>[4,2],("4",2)=>[4,1,1])
    cols=[findfirst(==(cycle_by_class[(u.classes[c].name,a)]),cycles) for (c,a) in t.classes]
    rows=[findfirst(==(p),partitions) for p in
          ([5,1],[4,2],[3,2,1],[6],[2,2,2],ones(Int,6))]
    @test t.scalar==CharTable(s).irr[rows,cols]
    @test t.cardClass==length.(conjugacy_classes(s))[cols]
  end

  @testset "G2 congruence sign" begin
    for (p,q) in ((2,2),(2,4),(2,8),(0,5),(0,7))
      w=coxgroup(:G,2)
      u=UnipotentClasses(w,p)
      t=UnipotentValues(u;q,classes=true)
      c=only(i for i in eachindex(u.classes) if u.classes[i].name=="G_2(a_1)")
      cols=findall(x->x[1]==c,t.classes)
      # The cuspidal almost character R_(1,epsilon)=s*q²*epsilon.
      almost=fourier(UnipotentCharacters(w))*t.scalar
      @test almost[8,cols]==(q%3==2 ? -1 : 1)*q^2*[1,-1,1]
      @test all(x->denominator(x)==1,t.scalar)
    end
  end

  @testset "E8 Springer pairs" begin
    # Hetz, arXiv:2309.09915v2, §§3.5–3.7 and Proposition 3.10:
    # every pair is a unipotent character sheaf, including E7-induced pairs.
    w=coxgroup(:E,8)
    h=UnipotentCharacters(w).harishChandra
    for (p,n) in ((2,146),(3,127),(5,117))
      u=UnipotentClasses(w,p)
      @test sum(ss->length(ss[:locsys]),u.springerseries)==n
      @test all(ss->get(ss,:hc,1)>0,u.springerseries)
      for ss in u.springerseries
        hc=get(ss,:hc,1)
        if hc>0
          @test length(ss[:locsys])==length(charnumbers(h[hc]))
        end
      end
    end
  end

  @testset "Exact field values and character identities" begin
    for (s,n,p) in ((:B,3,2),(:C,3,2),(:B,6,2),(:D,5,2),
                    (:B,4,3),(:C,6,3),(:D,8,3),(:G,2,2),(:G,2,3),
                    (:F,4,2),(:F,4,3),(:E,6,2),(:E,6,3),(:E,7,2),(:E,7,3))
      w=coxgroup(s,n)
      u=UnipotentClasses(w,p)
      for q in big(p).^(1:2)
        @testset "$s$n, q=$q" begin
          t=UnipotentValues(u;q,classes=true)
          d=degrees(UnipotentCharacters(w),q)
          id=only(j for (j,(c,a)) in enumerate(t.classes) if u.classes[c].dimBu==nref(w))
          @test t.scalar[:,id]==d
          @test all(isone,t.scalar[findfirst(isone,d),:])
          @test t.scalar[findfirst(==(q^nref(w)),d),:]==
                [j==id ? q^nref(w) : 0 for j in eachindex(t.classes)]
          @test sum(t.cardClass)==q^(2nref(w))
          @test all(x->x>0 && denominator(x)==1,t.cardClass)
          @test all(x->denominator(x)==1,t.scalar)
          @test !(eltype(t.scalar)<:Union{AbstractFloat,Complex{<:AbstractFloat}})
        end
      end
    end
  end

  @testset "Classical isogenies in characteristic two" begin
    for (s,n,forms) in ((:B,3,((:spin,7),(:sp,6),(:psp,6))),
                        (:D,4,((:spin,8),(:so,8),(:pso,8))))
      expected=UnipotentValues(UnipotentClasses(coxgroup(s,n),2);q=2,classes=true)
      for (form,dim) in forms
        t=UnipotentValues(UnipotentClasses(rootdatum(form,dim),2);q=2,classes=true)
        @test t.classes==expected.classes
        @test t.scalar==expected.scalar
        @test t.cardClass==expected.cardClass
      end
    end
  end

  @testset "E8 field-dependent Green function sign" begin
    w=coxgroup(:E,8)
    for (p,q) in ((2,2),(2,4),(3,3),(5,5),(5,25))
      u=UnipotentClasses(w,p)
      t=UnipotentValues(u;q=big(q),classes=true)
      @test all(x->denominator(x)==1,t.scalar)
      id=only(j for (j,(c,a)) in enumerate(t.classes) if u.classes[c].dimBu==nref(w))
      @test t.scalar[:,id]==degrees(UnipotentCharacters(w),big(q))
      @test sum(t.cardClass)==big(q)^(2nref(w))
      if p!=3
        # Lübeck, arXiv:2403.18190v2, Theorem 6.1: D8(a3)=E8(b6),
        # with a minus sign on the sign local system precisely for q≡-1 mod 3.
        c=only(i for i in eachindex(u.classes) if u.classes[i].name=="E_8(b_6)")
        cols=findall(x->x[1]==c,t.classes)
        almost=fourier(UnipotentCharacters(w))*t.scalar
        a=charinfo(u.classes[c].Au).positionDet
        r=findfirst(==([c,a]),u.springerseries[1][:locsys])
        @test almost[r,cols]==(q%3==2 ? -1 : 1)*big(q)^10*CharTable(u.classes[c].Au).irr[a,:]
        if q==2
          # Independent fixed-point counts on G/P_D4, §6, Step (6) of
          # the same paper. Integrality alone does not detect this sign.
          h=reflection_subgroup(w,2:5)
          mult=induction_table(h,w).scalar[:,charinfo(h).positionId]
          @test sort(vec(transpose(mult)*t.scalar[1:112,cols]))==[89825,92897,177889]
        end
      end
    end
  end
end

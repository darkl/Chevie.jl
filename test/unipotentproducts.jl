using Test, Chevie

# External products multiply character values and local-system functions.
# Match the mathematical labels: the table order need not be Kronecker order.
function unipotent_product_test(w1,w2,p,q)
  u1,u2,u=UnipotentClasses.((w1,w2,w1*w2),p)
  function xrows(u)
    reduce(vcat,map(u.springerseries)do s
      # The induced pair attached to the trivial relative character
      # distinguishes different cuspidal data on the same Levi.
      c,a=s[:locsys][charinfo(s[:relgroup]).positionId]
      pair=(u.classes[c].name,charinfo(u.classes[c].Au).charparams[a])
      [(Tuple(s[:levi]),pair,b) for b in charinfo(s[:relgroup]).charparams]
    end)
  end
  localcolumns(u,t)=[(u.classes[c].name,charinfo(u.classes[c].Au).charparams[a])
                      for (c,a) in t.locsys]
  function classcolumns(u,t)
    [(u.classes[c].name,classinfo(u.classes[c].Au).classparams[a]) for (c,a) in t.classes]
  end
  for table in (XTable,UnipotentValues), classes in (false,true)
    @testset "$(nameof(table)), classes=$classes" begin
      a,b,t=map(v->table(v;q,classes),(u1,u2,u))
      if table===XTable
        r1,r2,r=xrows.((u1,u2,u))
        productrows=[(Tuple(vcat(collect(x[1]),collect(y[1]).+rank(w1))),
                       (x[2][1]*","*y[2][1],vcat(x[2][2],y[2][2])),vcat(x[3],y[3]))
                       for (x,y) in cartesian(r1,r2)]
      else
        r1,r2,r=map(v->UnipotentCharacters(v.spets).charParams,(u1,u2,u))
        productrows=[vcat(x,y) for (x,y) in cartesian(r1,r2)]
      end
      c1,c2,c=classes ? map(classcolumns,(u1,u2,u),(a,b,t)) :
                       map(localcolumns,(u1,u2,u),(a,b,t))
      productcols=[(x[1]*","*y[1],vcat(x[2],y[2])) for (x,y) in cartesian(c1,c2)]
      rows=[only(findall(==(label),r)) for label in productrows]
      cols=[only(findall(==(label),c)) for label in productcols]
      @test t.scalar[rows,cols]==kron(a.scalar,b.scalar)
      if classes
        @test t.cardClass[cols]==kron(a.cardClass,b.cardClass)
        @test t.centClass[cols]==kron(a.centClass,b.centClass)
      else
        @test t.Y[cols,cols]==kron(a.Y,b.Y)
      end
    end
  end
end

@testset "Unipotent values of products" begin
  @testset "Products with partial power maps" begin
    a=deepcopy(CharTable(coxgroup(:A,2)))
    a.powermaps[3]=nothing
    b=CharTable(coxgroup(:A,1))
    t=prod([a,b])
    @test t.irr==kron(a.irr,b.irr)
    @test isnothing(t.powermaps[3])
    w=coxgroup(:A,2)*coxgroup(:A,1)
    @test t.powermaps[2]==[position_class(w,g^2) for g in classreps(w)]
  end
  @testset "Type A Frobenius action survives products" begin
    for w in (rootdatum(:sl,3)*rootdatum(:sl,2),
              rootdatum(:sl,2)*rootdatum(:sl,3),
              coxgroup(:G,2)*rootdatum(:sl,3),
              spets(rootdatum(:sl,3)*rootdatum(:sl,2)))
      u=UnipotentClasses(w,2)
      for classes in (false,true)
        @test_throws "incompatible field branch" XTable(u;q=2,classes)
      end
      t=UnipotentValues(u;q=2,classes=true)
      @test sum(t.cardClass)==big(2)^(2nref(w isa Spets ? Group(w) : w))
    end
    # SL3(2) x SL2(2) has six classes; the central quotient has the same values.
    u=UnipotentClasses(rootdatum(:pgl,3)*rootdatum(:sl,2),2)
    t=UnipotentValues(u;q=2,classes=true)
    @test sort(t.cardClass)==[1,3,21,42,63,126]
    # Trivial action depends on the exponent, not the order of C3 x C3.
    u=UnipotentClasses(rootdatum(:sl,3)*rootdatum(:sl,3),2)
    t=UnipotentValues(u;q=4,classes=true)
    @test length(t.classes)==25
    @test sum(t.cardClass)==big(4)^12
  end
  @testset "Split coset wrapper" begin
    w=coxgroup(:G,2)*coxgroup(:B,2)
    for table in (XTable,UnipotentValues), classes in (false,true)
      a,b=map(v->table(UnipotentClasses(v,2);q=2,classes),(w,spets(w)))
      @test a.scalar==b.scalar
    end
  end
  for (w1,w2,p,q) in ((coxgroup(:G,2),coxgroup(:G,2),0,5),
                      (coxgroup(:G,2),coxgroup(:B,2),2,2),
                      (coxgroup(:G,2),rootdatum(:sl,3),2,4),
                      (coxgroup(:G,2),rootdatum(:pgl,3),2,2),
                      (coxgroup(:E,8),coxgroup(:A,1),5,5))
    @testset "$w1 x $w2, q=$q" begin
      unipotent_product_test(w1,w2,p,q)
    end
  end
end

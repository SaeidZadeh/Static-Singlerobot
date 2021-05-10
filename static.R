library(pcalg)
library(igraph)
library(combinat)
library(statGraph)
library(arrangements)


areeq=function(a,b,p)
{
  for(i in 1:length(a[1,]))
    for(j in 1:length(a[1,]))
      if(b[i,j]!=a[p[i],p[j]])
        return(0)
  return(1)
}
areisogr=function(g1,g2)
{
  a1=as.matrix(get.adjacency(g1))
  a2=as.matrix(get.adjacency(g2))
  return(areiso(a1,a2))
}
areisowithany=function(g,G)
{
  for(i in 1:length(G))
    if(areisogr(g,G[i])==1)
      return(1)
  return(0)
}
areiso=function(a,b)
{
  if(length(a[1,])!=length(b[1,]))
    return(0)
  perm=permn(1:length(a[1,]))
  for(i in 1:length(perm))
    if(areeq(a,b,perm[i])==1)
      return(1)
  return(0)
}
indeg=function(a)
{
  c=rep(0,length(a[1,]))
  for(i in 1:length(a[1,]))
    c[i]=sum(a[,i])
  return(sort(c))
}
outdeg=function(a)
{
  c=rep(0,length(a[1,]))
  for(i in 1:length(a[1,]))
    c[i]=sum(a[i,])
  return(sort(c))
}
naiveisogr=function(g1,g2)
{
  a1=as.matrix(get.adjacency(g1))
  a2=as.matrix(get.adjacency(g2))
  return(naiveiso(a1,a2))
}
naiveiso=function(a,b)
{
  if(length(a[1,])!=length(b[1,]))
    return(0)
  a1=indeg(a)
  b1=indeg(b)
  for(i in 1:length(a[1,]))
    if(a1[i]!=b1[i])
      return(0)
  a1=outdeg(a)
  b1=outdeg(b)
  for(i in 1:length(a[1,]))
    if(a1[i]!=b1[i])
      return(0)
  return(1)
}
toadj=function(g)
{
  a=matrix(data=0,nrow=length(g@nodes),ncol=length(g@nodes))
  for(i in 1:length(g@nodes))
  {
    k=as.numeric(g@edgeL[[i]][[1]])
    if(length(k)>1)
      a[i,k]=1
    if(length(k)==1&&k!=i)
      a[i,k]=1
  }
  return(a)
}

outdeg2=function(a)
{
  b=rep(0,length(a[1,]))
  for(i in 1:length(a[1,]))
    b[i]=sum(a[i,])
  return(which(b>=2))
}
duplicable=function(a)
{
  g=graph.adjacency(a, mode = "directed",diag=TRUE)
  b=outdeg2(a)
  d=b
  c=setdiff(1:length(a[1,]),b)
  for(i in 1:length(c))
  {
    t=intersect(setdiff(as.numeric(subcomponent(g,i,mode="out")),i),b)
    if(length(t)>=1)
      d=c(b,i);
  }
  return(d)
}

indeg0=function(a)
{
  b=rep(0,length(a[1,]))
  for(i in 1:length(a[1,]))
    b[i]=sum(a[,i])
  return(which(b==0))
}
outdeg0=function(a)
{
  b=rep(0,length(a[1,]))
  for(i in 1:length(a[1,]))
    b[i]=sum(a[i,])
  return(which(b==0))
}

adjlist_find_paths <- function(a, n, m, path = list()) {
  path <- c(path, list(n))
  if (n == m) {
    return(list(path))
  } else {
    paths = list()
    for (child in a[[n]]) {
      if (!child %in% unlist(path)) {
        child_paths <- adjlist_find_paths(a, child, m, path)
        paths <- c(paths, child_paths)
      }
    }
    return(paths)
  }
}

# Find paths in graph from vertex source to vertex dest.
paths_from_to <- function(graph, source, dest) {
  a <- as_adj_list(graph, mode = "out")
  paths <- adjlist_find_paths(a, source, dest)
  lapply(paths, function(path) {V(graph)[unlist(path)]})
}


exec=function(texc,i,u)
{
  if(i==1)
    return(texc[3,u])
  if(i==2)
    return(texc[2,u])
  if(i>2)
    return(texc[1,u])
}
distnc=function(tdist,i,u,excec,k)
{
  return(tdist[u,i]*excec[1,k]+tdist[i,u]*excec[2,k])
}
ptoset=function(tdist,texc,i,u,k,excec)
{
  return(min(distnc(tdist,i,u,excec,k)+exec(texc,u,k)))
}
stoset=function(tdist,texc,u,b,k,excec)
{
  x=rep(0,length(u))
  for(i in 1:length(x))
    x[i]=ptoset(tdist,texc,u[i],b,k,excec)
  return(max(x))
}
lento=function(i,A,tdist,texc,p,excec)
{
  x=rep(0,length(p))
  for(k in 1:length(p)){
    if(length((p[[k]]))>1)
      for(j in seq(length(p[[k]]),2))
        x[k]=x[k]+stoset(tdist,texc,A[as.numeric(p[[k]][j])],A[as.numeric(p[[k]][j-1])],
                         as.numeric(p[[k]][j-1]),excec)
    x[k]=x[k]+ptoset(tdist,texc,i,A[as.numeric(p[[k]][1])],as.numeric(p[[k]][1]),excec)
  }
  return(max(x))
}
###################################################
distncli=function(tdist,i,u,excec,k)
{
  return(tdist[u,i]*excec[1,k]+tdist[i,u]*excec[2,k])
}
ptosetli=function(tdist,texc,i,u,k,excec)
{
  return(min(distnc(tdist,i,u,excec,k)+exec(texc,u,k)))
}
ptosetlimin=function(tdist,texc,i,u,k,excec)
{
  return(tdist[i,u]*excec[2,k])
}
stosetli=function(tdist,texc,u,b,k,excec)
{
  x=rep(0,length(u))
  for(i in 1:length(x))
    x[i]=ptosetli(tdist,texc,u[i],b,k,excec)
  return(max(x))
}
lentoli=function(i,A,tdist,texc,p,excec)
{
  x=rep(0,length(p))
  for(k in 1:length(p)){
    if(length((p[[k]]))>1)
      for(j in seq(length(p[[k]]),2))
        x[k]=x[k]+stosetli(tdist,texc,A[as.numeric(p[[k]][j])],A[as.numeric(p[[k]][j-1])],
                           as.numeric(p[[k]][j-1]),excec)
    x[k]=x[k]+ptosetli(tdist,texc,i,A[as.numeric(p[[k]][1])]
                       ,as.numeric(p[[k]][1]),excec)-ptosetlimin(
                         tdist,texc,i,A[as.numeric(p[[k]][1])],
                         as.numeric(p[[k]][1]),excec)
  }
  return(max(x))
}
memofun=function(A,p,excec,no.rob)
{
  x=sum(excec[1,])*32+sum(excec[2,])*32
  y=matrix(data=0,nrow=length(p),ncol=no.rob)
  for(ke in 1:no.rob){
    l=which(A==(ke+2))
    if(length(l)>0){
      for(k in 1:length(p)){
        wp=intersect(as.numeric(p[[k]]),l)
        if(length((p[[k]]))>1 && length(wp)>=1){
          y[k,ke]=max(excec[3,wp])*32
        }
      }
    }
  }
  return((x+max(y))/1024/1024)
}

  ddatplip=rep(0,10)
  ddatwodpp=rep(0,10)
  memolip=rep(0,10)
  memooursp=rep(0,10)
  xxour=rep(0,50)
  xxli=xxour
  for(iia in 1:50)
  {
    a=matrix(data=0,nrow=7,ncol=7)
    a[1,2]=1
    a[2,3]=1
    a[2,4]=1
    a[3,6]=1
    a[4,5]=1
    a[5,6]=1
    a[6,7]=1
    
    
    texc=matrix(data=0,nrow=3,ncol=length(a[1,]))
    texc[1,5]=0.44457
    texc[1,1]=4.4754
    texc[1,2]=0.00072
    texc[1,3]=0.00020
    texc[1,6]=6.61e-5
    texc[1,7]=0.00021
    texc[1,4]=0.00109
    texc[2,5]=0.15307
    texc[2,1]=1.5376
    texc[2,2]=0.00041
    texc[2,3]=7.7386e-5
    texc[2,6]=1.9370e-5
    texc[2,7]=0.00013
    texc[2,4]=0.00401
    texc[3,5]=0.04733
    texc[3,1]=0.46979
    texc[3,2]=0.00015
    texc[3,3]=3.4595e-5
    texc[3,6]=9.9644e-6
    texc[3,7]=4.7496e-5
    texc[3,4]=0.00027
    
    texc=texc*1000
    excec=matrix(data=0,nrow=3,ncol=length(a[1,]))
    excec[1,5]=24*3*256*256
    excec[1,1]=24*3*256*256*10
    excec[1,2]=1120*10
    excec[1,3]=1120*10
    excec[1,6]=1120*10
    excec[1,7]=1120*10
    excec[1,4]=24*3*256*256
    excec[2,5]=1120
    excec[2,1]=1120*10
    excec[2,2]=1120*10
    excec[2,3]=32*8
    excec[2,6]=1120*10
    excec[2,7]=1120
    excec[2,4]=24*3*256*256
    excec[3,5]=14619367
    excec[3,1]=11683901
    excec[3,2]=11684220
    excec[3,3]=7799083
    excec[3,6]=11253700
    excec[3,7]=11261700
    excec[3,4]=8010779
    
    excec[1:2,]=excec[1:2,]*0.125
    excec=excec/32
    
    
    
    gr=graph.adjacency(a, mode = "directed",diag=TRUE)
    o0=outdeg0(a)
    i0=indeg0(a)
    p=as.list(0)
    for(k in 1:length(i0))
      for(j in 1:length(o0))
        p=c(p,paths_from_to(gr,i0[k],o0[j]))
    p=p[2:length(p)];
    fp=matrix(data=0,nrow=6,ncol=6)
    fp[1,3]=0.439+abs(rnorm(1,0.188,0.087))
    fp[1,4]=0.439+abs(rnorm(1,0.188,0.087))
    fp[1,5]=0.439+abs(rnorm(1,0.188,0.087))
    fp[2,3]=0.439+abs(rnorm(1,0.188,0.087))
    fp[2,4]=0.439+abs(rnorm(1,0.188,0.087))
    fp[2,5]=0.439+abs(rnorm(1,0.188,0.087))
    fp[3,1]=0.417+abs(rnorm(1,0.367,0.365))
    fp[4,1]=0.417+abs(rnorm(1,0.367,0.365))
    fp[5,1]=0.417+abs(rnorm(1,0.367,0.365))
    fp[3,2]=0.417+abs(rnorm(1,0.367,0.365))
    fp[4,2]=0.417+abs(rnorm(1,0.367,0.365))
    fp[5,2]=0.417+abs(rnorm(1,0.367,0.365))
    fp[3,6]=(0.475+abs(rnorm(1,0.187,0.397)))
    fp[4,6]=(0.475+abs(rnorm(1,0.187,0.397)))
    fp[5,6]=(0.475+abs(rnorm(1,0.187,0.397)))
    fp[6,3]=(0.447+abs(rnorm(1,0.182,0.111)))
    fp[6,4]=(0.447+abs(rnorm(1,0.182,0.111)))
    fp[6,5]=(0.447+abs(rnorm(1,0.182,0.111)))
    fp[1,6]=(0.116+abs(rnorm(1,0.082,0.024)))
    fp[2,6]=(0.116+abs(rnorm(1,0.082,0.024)))
    fp[6,1]=(0.175+abs(rnorm(1,0.088,0.015)))
    fp[6,2]=(0.175+abs(rnorm(1,0.088,0.015)))
    fp[1,2]=(0.112+abs(rnorm(1,0.03,0.015)))
    fp[2,1]=(0.112+abs(rnorm(1,0.03,0.015)))
    fp[3,4]=(0.115+abs(rnorm(1,0.047,0.025)))
    fp[3,5]=(0.115+abs(rnorm(1,0.047,0.025)))
    fp[4,3]=(0.115+abs(rnorm(1,0.047,0.025)))
    fp[4,5]=(0.115+abs(rnorm(1,0.047,0.025)))
    fp[5,3]=(0.115+abs(rnorm(1,0.047,0.025)))
    fp[5,4]=(0.115+abs(rnorm(1,0.047,0.025)))
    
    
    
    
    
    gp=graph.adjacency(fp, mode = "undirected", weighted = TRUE, diag = FALSE)
    tdist <- shortest.paths(gp, algorithm = "dijkstra")
    x=rep(0,i-1);
    xli=x
    xzed=x
    l=rep(1,length(a[1,]))
    lp=l
    lpli=l
    for(k in 3:(i+1)){
      x[k-2]=lento(k,l,tdist,texc,p,excec)
      xli[k-2]=lentoli(k,l,tdist,texc,p,excec)
      xzed=x-xli
    }
    mem1=memofun(l,p,excec,i-1)
    mem1li=memofun(l,p,excec,i-1)
    memn=memofun(l,p,excec,i-1)
    xn=sqrt(sum(x^2))
    xnli=sqrt(sum(xli^2))
    y=x
    yli=xli
    yp=x
    xlitemp=xli
    xtemp=x
    allcomp=combinations(length(fp[1,]),length(a[1,]),replace=TRUE)
    zert=rep(0,length(allcomp[,1]))
    zertli=zert
    for(zed in 1:length(allcomp[,1])){
      for(k in 3:(i+1)){
        x[k-2]=lento(k,allcomp[zed,],tdist,texc,p,excec)
        xli[k-2]=lentoli(k,allcomp[zed,],tdist,texc,p,excec)
      }
      mem2=memofun(allcomp[zed,],p,excec,i-1)
      zert[zed]=sqrt(sum((x/xn)^2))*0.001
      zertli[zed]=sqrt(sum((xli/xnli)^2))*0.001
      if(sqrt(sum((yp/xn)^2)+(mem1/memn)^2)>=sqrt(sum((x/xn)^2)+(mem2/memn)^2)){
        for(k in 3:(i+1))
          yp[k-2]=x[k-2];
        lp=allcomp[zed,]
        xtemp=x
        mem1=mem2
      }
      if(sqrt(sum((yli/xnli)^2)+(mem1li/memn)^2)>=sqrt(sum((xli/xnli)^2)+(mem2/memn)^2)){
        lpli=allcomp[zed,]
        for(k in 3:(i+1)){
          yli[k-2]=xli[k-2];
        }
        xlitemp=yli
        mem1li=mem2
      }
      xzed=xtemp-xlitemp
    }
    xxli[iia]=sqrt(sum((yli/xnli)^2)+(mem1li/memn)^2)
    xxour[iia]=sqrt(sum((yp/xn)^2)+(mem1/memn)^2)
    print(iia)
  }
print(c(mean(xxli),sd(xxli),mean(xxour),sd(xxour)))
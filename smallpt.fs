open System            // smallpt, a Path Tracer by Kevin Beason, 2008
open System.IO
open System.Threading
open System.Threading.Tasks

type Vec = struct
    val x:double; val y:double; val z:double // position, also color (r,g,b)
    new (x) = { x = x; y = 0.0; z = 0.0 }
    new (x,y) = { x = x; y = y; z = 0.0 }
    new (x,y,z) = { x = x; y = y; z = z }
    static member (+) (a:Vec, b:Vec) = Vec(a.x+b.x,a.y+b.y,a.z+b.z)
    static member (-) (a:Vec, b:Vec) = Vec(a.x-b.x,a.y-b.y,a.z-b.z)
    static member (*) (a:Vec, b:double) = Vec(a.x*b,a.y*b,a.z*b)
    member this.mult (b:Vec) = Vec(this.x*b.x,this.y*b.y,this.z*b.z)
    member this.norm () = this * (1.0/sqrt(this.x*this.x+this.y*this.y+this.z*this.z))
    member this.dot (b:Vec) = this.x*b.x+this.y*b.y+this.z*b.z
    static member (%) (a:Vec, b:Vec) = Vec(a.y*b.z-a.z*b.y,a.z*b.x-a.x*b.z,a.x*b.y-a.y*b.x)
end

type Ray = struct
    val o:Vec; val d:Vec; 
    new (o,d) = { o = o; d = d }
end

type Refl_t = DIFF=0 | SPEC=1 | REFR=2  // material types, used in radiance() 

type Sphere = struct
    val rad:double        // radius 
    val p:Vec; val e:Vec; val c:Vec      // position, emission, color 
    val refl:Refl_t      // reflection type (DIFFuse, SPECular, REFRactive) 
    new (rad_,p_,e_,c_,refl_) = { rad = rad_; p = p_; e = e_; c = c_; refl = refl_ } 
    member this.intersect (r:Ray) = // returns distance, 0 if nohit 
        let op = this.p-r.o // Solve t^2*d.d + 2*t*(o-p).d + (o-p).(o-p)-R^2 = 0 
        let eps=1e-4
        let b=op.dot(r.d)
        let det=b*b-op.dot(op)+this.rad*this.rad
        if det<0.0 then 0.0
        else 
            let det=sqrt(det); 
            let t=b-det
            if t>eps then t
            else 
                let t=b+det
                if t>eps then t else 0.0
end

let spheres =
    [| //Scene: radius, position, emission, color, material 
        Sphere(1e5, Vec( 1e5+1.0,40.8,81.6), Vec(),Vec(0.75,0.25,0.25),Refl_t.DIFF)//Left 
        Sphere(1e5, Vec(-1e5+99.0,40.8,81.6),Vec(),Vec(0.25,0.25,0.75),Refl_t.DIFF)//Rght 
        Sphere(1e5, Vec(50.0,40.8, 1e5),     Vec(),Vec(0.75,0.75,0.75),Refl_t.DIFF)//Back 
        Sphere(1e5, Vec(50.0,40.8,-1e5+170.0), Vec(),Vec(),           Refl_t.DIFF)//Frnt 
        Sphere(1e5, Vec(50.0, 1e5, 81.6),    Vec(),Vec(0.75,0.75,0.75),Refl_t.DIFF)//Botm 
        Sphere(1e5, Vec(50.0,-1e5+81.6,81.6),Vec(),Vec(0.75,0.75,0.75),Refl_t.DIFF)//Top 
        Sphere(16.5,Vec(27.0,16.5,47.0),       Vec(),Vec(1.0,1.0,1.0)*0.999, Refl_t.SPEC)//Mirr 
        Sphere(16.5,Vec(73.0,16.5,78.0),       Vec(),Vec(1.0,1.0,1.0)*0.999, Refl_t.REFR)//Glas 
        Sphere(600.0, Vec(50.0,681.6-0.27,81.6),Vec(12.0,12.0,12.0),  Vec(), Refl_t.DIFF) //Lite 
    |]

let clamp (x) =
    match x with
    | x when x<0.0 -> 0.0 
    | x when x>1.0 -> 1.0 
    | _ -> x

let toInt (x) = int((System.Math.Pow(clamp(x),1.0/2.2)*255.0+0.5))

let intersect r (t:double byref) (id:int byref) =
    let n=spheres.Length
    t <- infinity
    for i=n-1 downto 0 do
        let d = spheres.[i].intersect(r)
        if (d > 0.0) && (d < t) then
            t <- d
            id <- i
    t<infinity

let rec radiance(r, depth, random:Random) =
    let mutable depth = depth
    let mutable t=infinity               // distance to intersection 
    let mutable id=0                     // id of intersected object 
    match intersect r (&t) (&id) with
    | false -> Vec() // if miss, return black 
    | true ->
        let obj = spheres.[id];           // the hit object 
        let x=r.o+r.d*t
        let n=(x-obj.p).norm();
        let nl=if n.dot(r.d)<0.0 then n else (n* -1.0)
        let mutable f=obj.c
        let p = if f.x>f.y && f.x>f.z then f.x else if f.y>f.z then f.y else f.z // max refl 
        depth <- depth+1
        match depth with
        | depth when depth > 101 -> obj.e
        | depth when depth > 5 && random.NextDouble() >= p -> obj.e
        | _ ->
            if (depth>5) then f <- f*(1.0/p)
            match (obj.refl) with              
            | Refl_t.DIFF ->                   // Ideal DIFFUSE reflection 
                let r1=2.0*System.Math.PI*random.NextDouble()
                let r2=random.NextDouble()
                let r2s=sqrt(r2)
                let w=nl
                let u=((if abs(w.x)>0.1 then Vec(0.0,1.0) else Vec(1.0))%w).norm()
                let v=w%u; 
                let d = (u*cos(r1)*r2s + v*sin(r1)*r2s + w*sqrt(1.0-r2)).norm(); 
                obj.e + f.mult(radiance(Ray(x,d),depth,random)); 
            | Refl_t.SPEC ->                   // Ideal SPECULAR reflection 
                obj.e + f.mult(radiance(Ray(x,r.d-n*2.0*n.dot(r.d)),depth,random));
            | _ ->                             // Ideal dielectric REFRACTION 
                let reflRay = Ray(x, r.d-n*2.0*n.dot(r.d))     
                let into = n.dot(nl)>0.0                // Ray from outside going in? 
                let nc=1.0
                let nt=1.5
                let nnt=if into then nc/nt else nt/nc
                let ddn=r.d.dot(nl)
                let cos2t=1.0-nnt*nnt*(1.0-ddn*ddn) 
                if (cos2t<0.0) then   // Total internal reflection 
                    obj.e + f.mult(radiance(reflRay,depth,random))
                else
                    let tdir = (r.d*nnt - n*((if into then 1.0 else -1.0)*(ddn*nnt+sqrt(cos2t)))).norm(); 
                    let a=nt-nc
                    let b=nt+nc
                    let R0=a*a/(b*b)
                    let c = 1.0-(if into then -ddn else tdir.dot(n)) 
                    let Re=R0+(1.0-R0)*c*c*c*c*c
                    let Tr=1.0-Re
                    let P=0.25+0.5*Re
                    let RP=Re/P
                    let TP=Tr/(1.0-P)
                    obj.e + f.mult(
                        if depth > 2 then
                            if random.NextDouble()<P then // Russian roulette 
                                radiance(reflRay,depth,random)*RP
                            else
                                radiance(Ray(x,tdir),depth,random)*TP
                        else 
                            radiance(reflRay,depth,random)*Re+radiance(Ray(x,tdir),depth,random)*Tr
                    ); 

[<EntryPoint>]
let main argv = 
    let w=1024
    let h=768
    let samps = if argv.Length=2 then (int argv.[1])/4 else 1 // # samples 
    let cam = Ray(Vec(50.0,52.0,295.6), Vec(0.0,-0.042612,-1.0).norm()); // cam pos, dir 
    let cx=Vec((double w)*0.5135/(double h))
    let cy=(cx%cam.d).norm()*0.5135
    let sample (random:Random) i =
        let x = i%w  
        let y = h-i/w-1
        let mutable color = Vec()
        for sy = 0 to 1 do               // 2x2 subpixel rows 
            for sx = 0 to 1 do 
                let mutable r=Vec()      // 2x2 subpixel cols 
                for s = 0 to samps-1 do 
                    let r1=2.0*random.NextDouble()
                    let dx= if r1<1.0 then sqrt(r1)-1.0 else 1.0-sqrt(2.0-r1); 
                    let r2=2.0*random.NextDouble()
                    let dy= if r2<1.0 then sqrt(r2)-1.0 else 1.0-sqrt(2.0-r2); 
                    let v0 = cx*( ( ((double sx)+0.5 + dx)/2.0 + (double x))/(double w) - 0.5)
                    let v1 = cy*( ( ((double sy)+0.5 + dy)/2.0 + (double y))/(double h) - 0.5)
                    let mutable d = cx*( ( ((double sx)+0.5 + dx)/2.0 + (double x))/(double w) - 0.5) + 
                                    cy*( ( ((double sy)+0.5 + dy)/2.0 + (double y))/(double h) - 0.5) + cam.d;
                    d <- d.norm()
                    r <- r + radiance(Ray(cam.o+d*140.0,d),0,random)*(1.0/(double samps)); 
                    // Camera rays are pushed ^^^^^ forward to start in interior 
                color <- color + Vec(clamp(r.x),clamp(r.y),clamp(r.z))*0.25
        color
    let c=Array.zeroCreate<Vec> (w*h)
    let stopwatch = System.Diagnostics.Stopwatch.StartNew()

    let multiThread = false
    if multiThread then
        let random = new ThreadLocal<_>(fun () -> new Random(12345))
        Parallel.For(0, w*h, (fun i -> c.[i] <- sample random.Value i)) |> ignore
    else
        let random = new Random(12345)
        for i = 0 to (w*h-1) do c.[i] <- sample random i

    Console.WriteLine("elapsed time: {0}", stopwatch.Elapsed);
    let sw = File.CreateText("smallptFS.ppm") // Write image to PPM file.    
    sw.Write("P3\n{0} {1}\n{2}\n", w, h, 255)
    for i = 0 to w*h-1 do
        sw.Write("{0} {1} {2}\n", toInt(c.[i].x), toInt(c.[i].y), toInt(c.[i].z)); 
    0 // return an integer exit code

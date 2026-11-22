// Tiny Vector3 / Quaternion (same maths as three.js r128, only the parts the physics needs) so the server has no extra dependency.
class Vector3{
  constructor(x=0,y=0,z=0){this.x=x;this.y=y;this.z=z}
  set(x,y,z){this.x=x;this.y=y;this.z=z;return this}
  copy(v){this.x=v.x;this.y=v.y;this.z=v.z;return this}
  clone(){return new Vector3(this.x,this.y,this.z)}
  add(v){this.x+=v.x;this.y+=v.y;this.z+=v.z;return this}
  sub(v){this.x-=v.x;this.y-=v.y;this.z-=v.z;return this}
  addScaledVector(v,s){this.x+=v.x*s;this.y+=v.y*s;this.z+=v.z*s;return this}
  multiplyScalar(s){this.x*=s;this.y*=s;this.z*=s;return this}
  divideScalar(s){return this.multiplyScalar(1/s)}
  negate(){this.x=-this.x;this.y=-this.y;this.z=-this.z;return this}
  dot(v){return this.x*v.x+this.y*v.y+this.z*v.z}
  lengthSq(){return this.x*this.x+this.y*this.y+this.z*this.z}
  length(){return Math.sqrt(this.lengthSq())}
  normalize(){return this.divideScalar(this.length()||1)}
  setLength(l){return this.normalize().multiplyScalar(l)}
  lerp(v,a){this.x+=(v.x-this.x)*a;this.y+=(v.y-this.y)*a;this.z+=(v.z-this.z)*a;return this}
  cross(v){return this.crossVectors(this,v)}
  crossVectors(a,b){const ax=a.x,ay=a.y,az=a.z,bx=b.x,by=b.y,bz=b.z;this.x=ay*bz-az*by;this.y=az*bx-ax*bz;this.z=ax*by-ay*bx;return this}
  applyQuaternion(q){const x=this.x,y=this.y,z=this.z,qx=q.x,qy=q.y,qz=q.z,qw=q.w;
    const ix=qw*x+qy*z-qz*y,iy=qw*y+qz*x-qx*z,iz=qw*z+qx*y-qy*x,iw=-qx*x-qy*y-qz*z;
    this.x=ix*qw+iw*-qx+iy*-qz-iz*-qy;this.y=iy*qw+iw*-qy+iz*-qx-ix*-qz;this.z=iz*qw+iw*-qz+ix*-qy-iy*-qx;return this}
  distanceTo(v){return Math.hypot(this.x-v.x,this.y-v.y,this.z-v.z)}
  toArray(){return [this.x,this.y,this.z]}
  fromArray(a){this.x=a[0];this.y=a[1];this.z=a[2];return this}
}
class Quaternion{
  constructor(x=0,y=0,z=0,w=1){this.x=x;this.y=y;this.z=z;this.w=w}
  set(x,y,z,w){this.x=x;this.y=y;this.z=z;this.w=w;return this}
  copy(q){this.x=q.x;this.y=q.y;this.z=q.z;this.w=q.w;return this}
  clone(){return new Quaternion(this.x,this.y,this.z,this.w)}
  conjugate(){this.x=-this.x;this.y=-this.y;this.z=-this.z;return this}
  invert(){return this.conjugate()}
  length(){return Math.sqrt(this.x*this.x+this.y*this.y+this.z*this.z+this.w*this.w)}
  normalize(){let l=this.length();if(l===0){this.x=this.y=this.z=0;this.w=1}else{l=1/l;this.x*=l;this.y*=l;this.z*=l;this.w*=l}return this}
  setFromAxisAngle(a,ang){const h=ang/2,s=Math.sin(h);this.x=a.x*s;this.y=a.y*s;this.z=a.z*s;this.w=Math.cos(h);return this}
  setFromUnitVectors(f,t){let r=f.dot(t)+1;
    if(r<1e-6){r=0;if(Math.abs(f.x)>Math.abs(f.z)){this.x=-f.y;this.y=f.x;this.z=0;this.w=r}else{this.x=0;this.y=-f.z;this.z=f.y;this.w=r}}
    else{this.x=f.y*t.z-f.z*t.y;this.y=f.z*t.x-f.x*t.z;this.z=f.x*t.y-f.y*t.x;this.w=r}
    return this.normalize()}
  multiplyQuaternions(a,b){const qax=a.x,qay=a.y,qaz=a.z,qaw=a.w,qbx=b.x,qby=b.y,qbz=b.z,qbw=b.w;
    this.x=qax*qbw+qaw*qbx+qay*qbz-qaz*qby;this.y=qay*qbw+qaw*qby+qaz*qbx-qax*qbz;
    this.z=qaz*qbw+qaw*qbz+qax*qby-qay*qbx;this.w=qaw*qbw-qax*qbx-qay*qby-qaz*qbz;return this}
  premultiply(q){return this.multiplyQuaternions(q,this)}
  slerp(qb,t){if(t===0)return this;if(t===1)return this.copy(qb);
    const x=this.x,y=this.y,z=this.z,w=this.w;let c=w*qb.w+x*qb.x+y*qb.y+z*qb.z;
    if(c<0){this.w=-qb.w;this.x=-qb.x;this.y=-qb.y;this.z=-qb.z;c=-c}else this.copy(qb);
    if(c>=1){this.w=w;this.x=x;this.y=y;this.z=z;return this}
    const sq=1-c*c;
    if(sq<=Number.EPSILON){const s=1-t;this.w=s*w+t*this.w;this.x=s*x+t*this.x;this.y=s*y+t*this.y;this.z=s*z+t*this.z;return this.normalize()}
    const sn=Math.sqrt(sq),ht=Math.atan2(sn,c),ra=Math.sin((1-t)*ht)/sn,rb=Math.sin(t*ht)/sn;
    this.w=w*ra+this.w*rb;this.x=x*ra+this.x*rb;this.y=y*ra+this.y*rb;this.z=z*ra+this.z*rb;return this}
  toArray(){return [this.x,this.y,this.z,this.w]}
  fromArray(a){this.x=a[0];this.y=a[1];this.z=a[2];this.w=a[3];return this}
}
module.exports={Vector3,Quaternion};

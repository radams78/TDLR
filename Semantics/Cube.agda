module Semantics.Cube where

record OpenCube (G : Groupoid) where
  field
    NWU : Fibration₂ G
    NWD : Fibration₂ G
    NEU : Fibration₂ G
    NED : Fibration₂ G
    SWU : Fibration₂ G
    SWD : Fibration₂ G
    SEU : Fibration₂ G
    SED : Fibration₂ G
    NW : Section₁ (Fibration-Eq₂ NWU NWD)
    SW : Section₂ (Fibration-Eq₂ SWU SWD)
    NE : Section₂ (Fibration-Eq₂ NEU NED)
    SE : Section₂ (Fibration-Eq₂ SEU SED)
    WU : Section₂ (Fibration-Eq₂ NWU SWU)
    WD : Section₂ (Fibration-Eq₂ NWD SWD)
    EU : Section₂ (Fibration-Eq₂ NEU SEU)
    ED : Section₂ (Fibration-Eq₂ NED SED)
    W : Section₁ (EQ₂ NW (Fibration-Eq₂-cong WU WD) SW)
    E : Section₁ (EQ₂ NE (Fibration-Eq₂-cong EU ED) SE)

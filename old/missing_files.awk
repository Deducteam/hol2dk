BEGIN{FS="[ .\t]"}
/^Error: Cannot find a physical path bound to logical path .*\.$/{printf"%s.v\n",$(NF-1);next}
/^Error: Cannot find a physical path bound to logical path$/{p=1;next}
{if(p){printf"%s.v\n",$1;p=0;next}}
/ Aucune règle pour fabriquer la cible « [^*]/{printf"%s.v\n",$10;next}
/ is required and has not been found in the loadpath!/{printf"%s.v\n",$10;next}

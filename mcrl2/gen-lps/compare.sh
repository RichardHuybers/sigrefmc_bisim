STRING=$1
lps2lts-dist -c --procs=4 --filter='action_labels' ${STRING}-b.lps ${STRING}-b.gcf
lps2lts-dist --filter='action_labels' ${STRING}-e.lps ${STRING}-e.gcf
ltsmin-compare -b ${STRING}-b.gcf ${STRING}-e.gcf

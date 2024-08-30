-- using default substitutions


select
	c_count,
	count(*) as custdist
from
	(
		select
                /*+ FK(o_custkey, c_custkey) */
			c_custkey,
			count(*)
		from
			customer join orders on
				c_custkey = o_custkey
				and o_comment not like '%special%requests%'
		group by
			c_custkey
	) as c_orders (c_custkey, c_count)
group by
	c_count
order by
	custdist desc,
	c_count desc;
limit -1;

SELECT COUNT(*) FROM comments as c, votes as v, users as u WHERE u.Id = c.UserId AND u.Id = v.UserId AND c.CreationDate>=CAST('2010-10-01 20:45:26' AS TIMESTAMP) AND c.CreationDate<=CAST('2014-09-05 12:51:17' AS TIMESTAMP) AND v.BountyAmount<=100 AND u.UpVotes=0 AND u.CreationDate<=CAST('2014-09-12 03:25:34' AS TIMESTAMP);